#!/usr/bin/env python3
"""Generate synthetic ARM64 instruction input/output cases with Unicorn 2.1.4.
No game files. Seeded, reproducible differential tests of the actual SSA lifter.
"""
import argparse,random,struct,json,collections,math
from unicorn import Uc,UC_ARCH_ARM64,UC_MODE_ARM
from unicorn import arm64_const as ac
from capstone import Cs,CS_ARCH_ARM64,CS_MODE_LITTLE_ENDIAN
p=argparse.ArgumentParser();p.add_argument('out');options=p.parse_args()
rng=random.Random(602601);dis=Cs(CS_ARCH_ARM64,CS_MODE_LITTLE_ENDIAN)
def gp(n):return getattr(ac,'UC_ARM64_REG_X'+str(n))
def qr(n):return getattr(ac,'UC_ARM64_REG_Q'+str(n))
mask=(1<<64)-1
def pack(xs,b):return sum((x&((1<<b)-1))<<(b*i) for i,x in enumerate(xs))
encodings=[]
def add(kind,word,vec=True):
 i=next(dis.disasm(struct.pack('<I',word),0),None)
 if i is None or i.mnemonic!=kind:raise ValueError((kind,hex(word),str(i)))
 encodings.append((kind,word,vec))
# Test register aliasing and both Q widths, element sizes, all variable shifts.
for q in (0,1):
 for sz in (0,1,2):
  for d,n in [(0,1),(1,1)]:
   add('rev64',0x0E200800|(q<<30)|(sz<<22)|(n<<5)|d)
 for kind,size in [('bif',3),('bit',2),('bsl',1)]:
  for d,n,m in [(0,1,2),(2,1,2),(1,1,2)]:
   add(kind,0x2E201C00|(q<<30)|(size<<22)|(m<<16)|(n<<5)|d)
 for sz in range(4 if q else 3):
  for d,n,m in [(0,1,2),(1,1,2),(2,1,2)]:
   add('ushl',0x2E204400|(q<<30)|(sz<<22)|(m<<16)|(n<<5)|d)
 for op,kind in [(0,'orr'),(1,'bic')]:
  for cmode in (1,3,5,7,9,11):
   for imm in (0,0x5a,255):
    add(kind,0x0F000400|(q<<30)|(op<<29)|((imm>>5)<<16)|(cmode<<12)|((imm&31)<<5)|1)
 for sz in (2,3) if q else (2,):
  for d,n in [(0,1),(1,1)]:
   add('fcmlt',0x0E20E800|(q<<30)|(sz<<22)|(n<<5)|d)
for sf in (0,1):
 for d,n in [(0,1),(1,1)]:
  add('rev16',0x5AC00400|(sf<<31)|(n<<5)|d,False)
for d,n in [(0,1),(1,1)]:add('rev32',0xDAC00800|(n<<5)|d,False)
for sf in (0,1):
 for typ in (0,1):
  for op,kind in [(2,'scvtf'),(3,'ucvtf')]:
   for fbits in (1,7,32 if not sf else 64):
    add(kind,0x1E000000|(sf<<31)|(typ<<22)|(op<<16)|((64-fbits)<<10)|(1<<5)|2)
# New families follow all existing encodings, preserving prior random inputs.
for q in (0,1):
 for sz in ((0,1) if q else (0,)):
  for d,n in [(0,0),(0,1),(1,1),(31,0),(0,31)]:
   add('frintp',0x0EA18800|(q<<30)|(sz<<22)|(n<<5)|d)
 for d,n in [(1,2),(1,1),(31,0),(0,31),(0,0)]:
  add('fcvtn2' if q else 'fcvtn',0x0E616800|(q<<30)|(n<<5)|d)
def f64bits(x):return struct.unpack('<Q',struct.pack('<d',x))[0]
f32pool=[0,0x80000000,1,0x80000001,0x007fffff,0x807fffff,0x3f000000,0xbf000000,0x3f7fffff,0xbf7fffff,0x3f800001,0xbf800001,0x4affffff,0x4b000000,0x7f7fffff,0xff7fffff,0x7f800000,0xff800000,0x7fc01234,0xffc01234,0x7f801234,0xff801234]
f64pool=[0,1<<63,1,(1<<63)|1,0x000fffffffffffff,0x800fffffffffffff,0x7fefffffffffffff,0xffefffffffffffff,0x7ff0000000000000,0xfff0000000000000,0x7ff8000000001234,0xfff8000000001234,0x7ff0000000001234,0xfff0000000001234]
for x in [0.5,-0.5,1.,-1.,math.nextafter(1.,0.),math.nextafter(1.,2.),math.nextafter(-1.,0.),math.nextafter(-1.,-2.),1.+2.**-24,-1.-2.**-24,math.nextafter(1.+2.**-24,2.),math.nextafter(1.+2.**-24,0.),2.**-149,2.**-150,3.*2.**-150,-2.**-150,(2.-2.**-23)*2.**127,(2.-2.**-24)*2.**127,2.**23-0.5,2.**52-0.5]:f64pool.append(f64bits(x))
rows=[];counts=collections.Counter()
for kind,word,vec in encodings:
 d=word&31
 for it in range(128 if kind in ('frintp','fcvtn','fcvtn2') else 8):
  g=[rng.getrandbits(64) for _ in range(34)];v=[rng.getrandbits(128) for _ in range(32)]
  g[27]=0x3000
  if kind in ('fcvtn','fcvtn2','frintp'):
   bits=32 if kind=='frintp' and not (word>>22)&1 else 64
   pool=f32pool if bits==32 else f64pool
   values=[pool[(it+k)%len(pool)] if it<len(pool) else rng.getrandbits(bits) for k in range(128//bits)]
   v[(word>>5)&31]=pack(values,bits)
  if kind=='ushl':
   size=1<<((word>>22)&3);bits=size*8;shifts=[-128,-bits-1,-bits,-bits+1,-1,0,1,bits-1,bits,bits+1,127]
   v[(word>>16)&31]=pack([rng.choice(shifts) for _ in range(16//size)],bits)
  if kind=='fcmlt':
   bits=64 if (word>>22)&1 else 32
   pool=[0,1<<(bits-1),1,1<<(bits-1)|1,0x7fc01234 if bits==32 else 0x7ff8000000001234,
         0x3f800000 if bits==32 else 0x3ff0000000000000,0xbf800000 if bits==32 else 0xbff0000000000000,
         0x7f800000 if bits==32 else 0x7ff0000000000000,0xff800000 if bits==32 else 0xfff0000000000000]
   v[(word>>5)&31]=pack([rng.choice(pool) for _ in range(128//bits)],bits)
  if kind in ('scvtf','ucvtf') and it<5:g[(word>>5)&31]=[0,1,mask,1<<63,(1<<63)-1][it]
  u=Uc(UC_ARCH_ARM64,UC_MODE_ARM);u.mem_map(0x1000,0x1000);u.mem_map(0x3000,0x1000)
  u.mem_write(0x1000,struct.pack('<I',word))
  for n in range(31):u.reg_write(gp(n),g[n])
  for n in range(32):u.reg_write(qr(n),v[n])
  u.reg_write(ac.UC_ARM64_REG_FPCR,0)
  u.emu_start(0x1000,0x1004,count=1)
  actual=u.reg_read(qr(d) if vec else gp(d))
  expected=[actual&mask,actual>>64] if vec else [actual&mask]
  rows.append(dict(Kind=kind,Word=word,Destination=d,Vector=vec,Gp=g,Vectors=[half for z in v for half in (z&mask,z>>64)],Expected=expected,Fpcr=0));counts[kind]+=1
with open(options.out,'w') as f:json.dump(rows,f,separators=(',',':'))
print('synthetic oracle cases',len(rows),dict(counts))
