from pathlib import Path
import sys,json,struct,hashlib,gc
sys.path[:0]=['/data/workspace/recovery-workflow/.deps','/data/workspace/recovery-workflow']
from method_evidence import Elf
from unicorn import Uc,UC_ARCH_ARM64,UC_MODE_ARM,UC_HOOK_CODE,UC_HOOK_MEM_INVALID,UcError
from unicorn.arm64_const import *
out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
elf=Elf(Path('/data/workspace/work/libil2cpp.so'));body=elf.read(0x20738A0,0x20738D8)
specs={'A':{'lengths':[2,2],'lower':[-5,7],'items':[11,12,13,14]},'B':{'lengths':[3,1],'lower':[10,-20],'items':[91,92,93]}}
cases=[]
for mode in ['call','field']:
 for array in ['A',None]:
  for throw in [None,'row','col']+(['array'] if mode=='call' else []):
   cases.append({'id':f'{mode}-{array}-{throw}','mode':mode,'array':array,'row':0,'col':0,'throw_on':throw})
 for row,col in [(1,1),(-1,0),(0,-1),(2,0),(0,2)]:
  cases.append({'id':f'{mode}-index-{row}-{col}','mode':mode,'array':'A','row':row,'col':col,'throw_on':None})
 for stage in ['row','col']:
  cases.append({'id':f'{mode}-swap-{stage}','mode':mode,'array':'A','row':0,'col':0,'throw_on':None,'swap_after':stage})
def native(name,row,col):
 u=Uc(UC_ARCH_ARM64,UC_MODE_ARM)
 for a,size in [(0x2073000,4096),(0x2355000,4096),(0x10000000,0x10000),(0x11000000,0x10000),(0x12000000,4096)]:u.mem_map(a,size)
 u.mem_write(0x20738A0,body)
 p=0x10000000;b=p+0x2000
 if name:
  s=specs[name];u.mem_write(p+16,struct.pack('<QQ',b,len(s['items'])))
  for d in range(2):u.mem_write(b+16*d,struct.pack('<Qi',s['lengths'][d],s['lower'][d]))
  for n,item in enumerate(s['items']):u.mem_write(p+32+8*n,struct.pack('<Q',item))
 u.reg_write(UC_ARM64_REG_X0,p if name else 0);u.reg_write(UC_ARM64_REG_X1,row&((1<<64)-1));u.reg_write(UC_ARM64_REG_X2,col&((1<<64)-1))
 u.reg_write(UC_ARM64_REG_SP,0x11008000);u.reg_write(UC_ARM64_REG_LR,0x12000000)
 r={'returned':None,'exception':None}
 def code(uc,a,size,_):
  if a==0x2355668:r['exception']='IndexOutOfRangeException';u.emu_stop()
  if a==0x12000000:r['returned']=u.reg_read(UC_ARM64_REG_X0);u.emu_stop()
 def invalid(uc,access,a,size,value,_):
  r['exception']='NullReferenceException' if a<4096 else 'UNEXPECTED';u.emu_stop();return False
 hs=[u.hook_add(UC_HOOK_CODE,code),u.hook_add(UC_HOOK_MEM_INVALID,invalid)]
 try:u.emu_start(0x20738A0,0x12000004,count=100)
 except UcError:
  if not r['exception']:raise
 for h in hs:u.hook_del(h)
 del u;gc.collect();assert r['exception']!='UNEXPECTED';return r
rows=[]
for c in cases:
 events=[];current=c['array'];captured=current;exc=None
 # Synthetic argument producers make the ABI contract observable: all run before entering the original helper.
 stages=(['array'] if c['mode']=='call' else [])+['row','col']
 for stage in stages:
  events.append([stage,c['array'] if stage=='array' else c[stage]])
  if c['throw_on']==stage:exc='InvalidOperationException';break
  if c.get('swap_after')==stage:current='B'
 result={'returned':None,'exception':exc} if exc else native(captured,c['row'],c['col'])
 rows.append({'id':c['id'],**result,'events':events,'current':current})
(out/'cases.json').write_text(json.dumps({'arrays':specs,'cases':cases},indent=2)+'\n')
(out/'oracle.json').write_text(json.dumps({'body_sha256':hashlib.sha256(body).hexdigest(),'scope':'Synthetic argument producer events followed by original complete 56-byte native getter; compare real MdElementRead and BodyEmitter output.','cases':rows},indent=2)+'\n')
print('EFFECT_BOUNDARY_NATIVE',len(rows))
