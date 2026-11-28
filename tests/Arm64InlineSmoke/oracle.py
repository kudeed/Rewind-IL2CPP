import json,struct,sys
from unicorn import Uc,UC_ARCH_ARM64,UC_MODE_ARM
from unicorn.arm64_const import UC_ARM64_REG_X0,UC_ARM64_REG_X1,UC_ARM64_REG_X2,UC_ARM64_REG_SP,UC_ARM64_REG_LR,UC_ARM64_REG_X29
RET=0xd65f03c0
bl=lambda at,to:0x94000000|(((to-at)//4)&0x3ffffff)
def caller(repeat=False):
 words=[0xa9bf7be1,bl(0x1004,0x2000),0x91000c00]
 if repeat:words.append(bl(0x1000+4*len(words),0x2000))
 return words+[0xa8c17be1,0xf9000020,0x910003e3,0xf9000423,0xf900083d,0xf9000c3e,RET]
helpers={
 'scalar':[0x91001c00,RET],
 'branch':[0xb4000060,0x91001c00,RET,0xd2800540,RET],
 'loop':[0xb4000080,0x91000442,0xf1000400,0x54ffffc1,0xaa0203e0,RET],
 'foreign':[0xa9bf7bfd,bl(0x2004,0x3000),0xa8c17bfd,RET],
 'closure':[0xf9400002,0xf9400043,0x91001c63,0xf9000043,0xaa0303e0,RET],
}
cases=[]
for kind,helper in helpers.items():
 for repeat in [False,True]:
  if kind=='closure' and repeat:continue
  for value in ([0,1,3,9] if kind=='loop' else [0,1,0xffffffffffffffff,0x7fffffffffffffff]):
   uc=Uc(UC_ARCH_ARM64,UC_MODE_ARM);uc.mem_map(0x1000,0x10000)
   funcs={'4096':caller(repeat),'8192':helper}
   if kind=='foreign':funcs['12288']=[0x91001c00,RET]
   for address,words in funcs.items():uc.mem_write(int(address),b''.join(struct.pack('<I',w) for w in words))
   initial={'36864':0,'36872':0,'36880':0,'36888':0,'37120':0x9200,'37376':value}
   for address,bits in initial.items():uc.mem_write(int(address),struct.pack('<Q',bits))
   arg=0x9100 if kind=='closure' else value
   uc.reg_write(UC_ARM64_REG_X0,arg);uc.reg_write(UC_ARM64_REG_X1,0x9000);uc.reg_write(UC_ARM64_REG_X2,11)
   uc.reg_write(UC_ARM64_REG_SP,0xf000);uc.reg_write(UC_ARM64_REG_X29,0xbad0);uc.reg_write(UC_ARM64_REG_LR,0x8000)
   uc.emu_start(0x1000,0x8000,count=10000)
   assert uc.reg_read(UC_ARM64_REG_SP)==0xf000
   assert uc.reg_read(UC_ARM64_REG_X29)==0xbad0
   assert uc.reg_read(UC_ARM64_REG_LR)==0x8000
   result=uc.reg_read(UC_ARM64_REG_X0)
   expected={address:struct.unpack('<Q',uc.mem_read(int(address),8))[0] for address in initial}
   cases.append(dict(Name=f'{kind}-{int(repeat)}-{value:X}',Functions=funcs,Args=[arg,0x9000,11],Memory=initial,Expected=result,ExpectedMemory=expected))
open(sys.argv[1],'w').write(json.dumps(cases,indent=2)+'\n')
print('ARM64_INLINE_NATIVE_ORACLE cases='+str(len(cases)))
