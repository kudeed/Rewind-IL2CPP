import json
import struct
import sys
from unicorn import Uc, UC_ARCH_ARM64, UC_MODE_ARM
from unicorn.arm64_const import UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2, UC_ARM64_REG_SP, UC_ARM64_REG_LR, UC_ARM64_REG_X29

def branch(at, target):
    return 0x14000000 | (((target - at) // 4) & 0x3ffffff)

cases = []
for kind, effects in {
    'empty': [],
    'load': [0xf9400529],
    'load-add': [0xf9400529, 0x91002129],
    'load-store-load': [0xf9400529, 0xf9000829, 0xf9400129],
}.items():
    for value in [0, 1, 17, 255, 0xffffffff, 0x100000001, 0x7fffffffffffffff, 0xffffffffffffffff]:
        functions = {
            '4096': [0xaa0103e9, branch(0x1004, 0x2000), 0xf9400122, 0x8b020000, 0xf9000020, 0xd65f03c0],
            '8192': effects + [branch(0x2000 + len(effects) * 4, 0x1008)],
        }
        memory = {'36864': 7, '36872': 0x9200, '36880': 0, '37376': 0x9300, '37384': 19, '37632': 23}
        uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
        uc.mem_map(0x1000, 0x10000)
        for address, words in functions.items():
            uc.mem_write(int(address), b''.join(struct.pack('<I', w) for w in words))
        for address, bits in memory.items():
            uc.mem_write(int(address), struct.pack('<Q', bits))
        for reg, bits in [(UC_ARM64_REG_X0, value), (UC_ARM64_REG_X1, 0x9000), (UC_ARM64_REG_X2, 11), (UC_ARM64_REG_SP, 0xf000), (UC_ARM64_REG_X29, 0xbad0), (UC_ARM64_REG_LR, 0x8000)]:
            uc.reg_write(reg, bits)
        uc.emu_start(0x1000, 0x8000, count=10000)
        assert uc.reg_read(UC_ARM64_REG_SP) == 0xf000
        assert uc.reg_read(UC_ARM64_REG_LR) == 0x8000
        expected = {address: struct.unpack('<Q', uc.mem_read(int(address), 8))[0] for address in memory}
        cases.append(dict(Name=f'{kind}-{value:X}', Functions=functions, Args=[value, 0x9000, 11], Memory=memory, Expected=uc.reg_read(UC_ARM64_REG_X0), ExpectedMemory=expected))
with open(sys.argv[1], 'w') as stream:
    json.dump(cases, stream, indent=2)
print('ARM64_BRANCH_RETURN_NATIVE_ORACLE cases=' + str(len(cases)))
