"""Execute original ARM64 bytes. Managed call boundaries are explicit, recorded fixtures."""
from pathlib import Path
import sys,json,hashlib,struct,gc
workflow=Path(sys.argv[3]) if len(sys.argv)>3 else Path('/data/workspace/recovery-workflow')
sys.path[:0]=[str(workflow/'.deps'),str(workflow)]
from method_evidence import Elf
from unicorn import Uc,UC_ARCH_ARM64,UC_MODE_ARM,UC_HOOK_CODE,UC_HOOK_MEM_INVALID,UcError
from unicorn.arm64_const import *
B=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/data/workspace/rewind-null-proof-v175/mdarray-proof')
B.mkdir(parents=True,exist_ok=True)
NATIVE=Path(sys.argv[2]) if len(sys.argv)>2 else Path('/data/workspace/work/libil2cpp.so')
elf=Elf(NATIVE)
ranges={'scan':(0x257D8AC,0x257D964),'get':(0x20738A0,0x20738D8),'corners':(0x259A43C,0x259AC30)}
bodies={k:elf.read(a,z) for k,(a,z) in ranges.items()}
assert hashlib.sha256(NATIVE.read_bytes()).hexdigest()=='f0808ccac104a950c6b99a3f4a148c21ae0daed078105714b14ac2b58f1dd583'
cases=[]
def array(name,rows,cols,lower=(0,0),null_at=()):
 return {'id':name,'lengths':[rows,cols],'lower':list(lower),'items':[None if k in null_at else (ord(name[0])*1000+k+1) for k in range(rows*cols)]}
def case(mode,name,arrays,**kw):
 cases.append({'id':mode+'-'+name,'mode':mode,'arrays':arrays,'initial':arrays[0]['id'] if arrays else None,**kw})
for lower in [(0,0),(-3,7),(-2147483648,2147483644)]:
 for rows,cols in [(0,0),(0,3),(3,0),(1,1),(2,3)]:
  a=array('A',rows,cols,lower,null_at=(0,))
  indices=set([(0,0),(-1,0),(0,-1),(rows,0),(0,cols),(max(0,rows-1),max(0,cols-1)),(-2147483648,2147483647)])
  for r,c in sorted(indices):case('get',f'{rows}x{cols}-{lower[0]}-{lower[1]}-{r}-{c}',[a],row=r,col=c)
for r,c in [(0,0),(-1,0),(2147483647,0)]:case('get',f'null-{r}-{c}',[],row=r,col=c)
for lower in [(0,0),(-2,6),(-2147483648,2147483644)]:
 for rows,cols in [(0,0),(0,3),(3,0),(1,1),(2,3),(3,2)]:
  case('scan',f'{rows}x{cols}-{lower[0]}-{lower[1]}',[array('A',rows,cols,lower)])
case('scan','null',[])
case('scan','null-element-first',[array('A',2,3,null_at=(0,))])
case('scan','null-element-late',[array('A',2,3,null_at=(4,))])
for n in [0,3]:case('scan',f'callback-throw-{n}',[array('A',2,3)],throw_callback=n)
case('scan','callback-array-null',[array('A',2,3)],replacements=[{'kind':'callback','at':0,'to':None}])
case('scan','callback-array-shrink',[array('A',2,3),array('B',1,1,(-4,6))],replacements=[{'kind':'callback','at':0,'to':'B'}])
case('scan','callback-array-swap',[array('A',2,3),array('B',3,2,(4,-6))],replacements=[{'kind':'callback','at':0,'to':'B'}])
for replacement in [None,'B']:
 case('scan','length-array-'+str(replacement),[array('A',2,3),array('B',0,3)],replacements=[{'kind':'length','at':1,'to':replacement}])
for lower in [(0,0),(-4,7),(-2147483648,2147483644)]:
 for rows,cols in [(0,0),(0,3),(3,0),(1,1),(2,3),(3,2)]:
  case('corners',f'{rows}x{cols}-{lower[0]}-{lower[1]}',[array('A',rows,cols,lower)])
case('corners','null',[])
case('corners','null-elements',[array('A',2,3,null_at=(0,2,3,5))])
case('corners','null-controller',[array('A',2,3)],null_controller=True)
for n in [0,1,3]:case('corners',f'callback-throw-{n}',[array('A',2,3)],throw_callback=n)
for n in [0,1,2]:case('corners',f'callback-null-{n}',[array('A',2,3)],replacements=[{'kind':'callback','at':n,'to':None}])
# Four fields can intentionally change at external boundaries. The fourth read uses D, its column comes from fresh E.
arrays=[array('A',2,3,(-2,5)),array('B',3,2,(3,-6)),array('C',2,4,(-7,4)),array('D',4,5,(-9,10))]
swaps=[{'kind':'callback','at':i,'to':name} for i,name in enumerate(['B','C','D'])]
for name,extra in [('smaller',array('E',6,2,(15,-13))),('larger',array('E',6,6,(-2,7))),('zero',array('E',6,0)),('null',None)]:
 case('corners','fresh-fourth-'+name,arrays+([extra] if extra else []),replacements=swaps+[{'kind':'length','at':2,'to':'E' if extra else None}])
# Changing the field after the final length does not change the saved array used by the final load.
case('corners','final-length-swap',arrays+[array('E',2,2)],replacements=swaps+[{'kind':'length','at':3,'to':'E'}])
B.joinpath('cases.json').write_text(json.dumps(cases,indent=2)+'\n')
MASK=(1<<64)-1
ARENA=0x10000000;STACK=0x18000000;STOP=0x19000000;MANAGER=ARENA+0x100;STATE=ARENA+0x300;CONTROLLER=ARENA+0x500
CALL_LENGTH=0x401700C;CALL_REFRESH=0x2473674;CALL_POSITION=0x2599688;THROW_NULL=0x2355660;THROW_BOUNDS=0x2355668
def run(c):
 u=Uc(UC_ARCH_ARM64,UC_MODE_ARM);mapped=set()
 def maprange(a,size):
  for p in range(a&~0xfff,(a+size+0xfff)&~0xfff,4096):
   if p not in mapped:u.mem_map(p,4096);mapped.add(p)
 maprange(ARENA,0x200000);maprange(STACK,0x10000);maprange(STOP,4096)
 a,z=ranges[c['mode']];maprange(a,z-a);u.mem_write(a,bodies[c['mode']])
 for target in [CALL_LENGTH,CALL_REFRESH,CALL_POSITION,THROW_NULL,THROW_BOUNDS]:maprange(target,4)
 def put64(a,v):u.mem_write(a,struct.pack('<Q',v&MASK))
 def get64(a):return struct.unpack('<Q',u.mem_read(a,8))[0]
 items={};addresses={};specs={};reverse={}
 for index,spec in enumerate(c['arrays']):
  addr=ARENA+0x1000+index*0x10000;bounds=addr+0x8000
  addresses[spec['id']]=addr;reverse[addr]=spec['id'];specs[addr]=spec
  put64(addr+16,bounds);put64(addr+24,len(spec['items']))
  for dim in range(2):
   put64(bounds+16*dim,spec['lengths'][dim]);u.mem_write(bounds+16*dim+8,struct.pack('<i',spec['lower'][dim]))
  for n,item in enumerate(spec['items']):
   ptr=0 if item is None else ARENA+0x100000+item*8
   if ptr:items[ptr]=item
   put64(addr+32+n*8,ptr)
 initial=addresses.get(c['initial'],0)
 put64(MANAGER+0x68,initial);put64(STATE+0x28,initial);u.mem_write(STATE+0x10,struct.pack('<i',1))
 u.reg_write(UC_ARM64_REG_SP,STACK+0x8000);u.reg_write(UC_ARM64_REG_LR,STOP)
 if c['mode']=='scan':u.reg_write(UC_ARM64_REG_X0,MANAGER);start=a
 elif c['mode']=='get':
  u.reg_write(UC_ARM64_REG_X0,initial);u.reg_write(UC_ARM64_REG_X1,c['row']&MASK);u.reg_write(UC_ARM64_REG_X2,c['col']&MASK);start=a
 else:
  u.reg_write(UC_ARM64_REG_X20,STATE);u.reg_write(UC_ARM64_REG_X19,0 if c.get('null_controller') else CONTROLLER);start=0x259A594
 events=[];counts={'callback':0,'length':0};result={'returned':None,'exception':None,'completed':False}
 def fail(exc):result['exception']=exc;u.emu_stop()
 def replace(kind,n):
  for r in c.get('replacements',[]):
   if r['kind']==kind and r['at']==n:
    ptr=addresses.get(r['to'],0);put64(MANAGER+0x68,ptr);put64(STATE+0x28,ptr)
 def boundary(kind):
  n=counts[kind];counts[kind]+=1
  if kind=='callback' and c.get('throw_callback')==n:fail('InvalidOperationException');return False
  replace(kind,n);return True
 def code(uc,address,size,_):
  if address==STOP:
   result['completed']=True
   if c['mode']=='get':result['returned']=items.get(u.reg_read(UC_ARM64_REG_X0)) if u.reg_read(UC_ARM64_REG_X0) else None
   u.emu_stop()
  elif address in [THROW_NULL,THROW_BOUNDS]:fail('NullReferenceException' if address==THROW_NULL else 'IndexOutOfRangeException')
  elif address==CALL_LENGTH:
   ptr=u.reg_read(UC_ARM64_REG_X0);dim=u.reg_read(UC_ARM64_REG_X1)&0xffffffff
   if not ptr:fail('NullReferenceException');return
   length=specs[ptr]['lengths'][dim];events.append(['length',reverse[ptr],dim,length]);boundary('length');u.reg_write(UC_ARM64_REG_X0,length);u.reg_write(UC_ARM64_REG_PC,u.reg_read(UC_ARM64_REG_LR))
  elif address==CALL_REFRESH:
   ptr=u.reg_read(UC_ARM64_REG_X0)
   if not ptr:fail('NullReferenceException');return
   events.append(['refresh',items[ptr]])
   if boundary('callback'):u.reg_write(UC_ARM64_REG_PC,u.reg_read(UC_ARM64_REG_LR))
  elif address==CALL_POSITION:
   ptr=u.reg_read(UC_ARM64_REG_X1);events.append(['position',items.get(ptr) if ptr else None])
   if boundary('callback'):
    if counts['callback']==4:result['completed']=True;u.emu_stop()
    else:
     for r,v in [(UC_ARM64_REG_S0,1.0),(UC_ARM64_REG_S1,2.0),(UC_ARM64_REG_S2,3.0)]:u.reg_write(r,struct.unpack('<I',struct.pack('<f',v))[0])
     u.reg_write(UC_ARM64_REG_PC,u.reg_read(UC_ARM64_REG_LR))
 def invalid(uc,access,address,size,value,_):
  if address<0x1000:fail('NullReferenceException')
  else:fail('UNEXPECTED_MEMORY_'+hex(address))
  return False
 hooks=[u.hook_add(UC_HOOK_CODE,code),u.hook_add(UC_HOOK_MEM_INVALID,invalid)]
 try:u.emu_start(start,STOP+4,count=30000)
 except UcError as ex:
  if not result['exception']:result['exception']='UNEXPECTED_UNICORN_'+str(ex)
 if not result['completed'] and not result['exception']:raise RuntimeError('instruction limit '+c['id'])
 if result['exception'] and result['exception'].startswith('UNEXPECTED'):raise RuntimeError(c['id']+' '+result['exception'])
 result['events']=events
 result['current']=reverse.get(get64(STATE+0x28 if c['mode']=='corners' else MANAGER+0x68))
 result['state']=struct.unpack('<i',u.mem_read(STATE+0x10,4))[0] if c['mode']=='corners' else None
 for h in hooks:u.hook_del(h)
 del u;gc.collect()
 return {'id':c['id'],**result}
out=[run(c) for c in cases]
proof={'native_sha256':hashlib.sha256(NATIVE.read_bytes()).hexdigest(),'cases_sha256':hashlib.sha256(B.joinpath('cases.json').read_bytes()).hexdigest(),'bodies':{k:{'start':hex(ranges[k][0]),'end':hex(ranges[k][1]),'sha256':hashlib.sha256(v).hexdigest()} for k,v in bodies.items()},'boundary_contract':'Execute original bytes; Array.GetLength and callback callees are instrumented only at original native calls. Nonzero lower bounds are represented in native bounds records and real CLR arrays. Camera starts at state-1 arm entry and stops after fourth position call; later animation is outside this fixture.','cases':out}
B.joinpath('native-oracle.json').write_text(json.dumps(proof,indent=2)+'\n')
print('MD_NATIVE_ORACLE',len(out),'cases', {mode:sum(c['mode']==mode for c in cases) for mode in ranges})
