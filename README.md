
compile the asm in the chap4 of CSAPP y86_64 program into a self defined binary file
```
> cargo run -- ../example.ysm
Length: 205 (0xcd) bytes
0000:   20 00 00 00  00 00 00 00  02 00 00 00  00 00 00 00    ...............
0010:   00 00 00 00  00 00 00 00  40 00 00 00  00 00 00 00   ........@.......
0020:   8d 00 00 00  00 00 00 00  00 02 00 00  00 00 00 00   ................
0030:   cd 00 00 00  00 00 00 00  00 00 00 00  00 00 00 00   ................
0040:   0d 00 0d 00  0d 00 00 00  c0 00 c0 00  c0 00 00 00   ................
0050:   00 0b 00 0b  00 0b 00 00  00 a0 00 a0  00 a0 00 00   ................
0060:   30 f4 00 02  00 00 00 00  00 00 80 34  00 00 00 00   0..........4....
0070:   00 00 00 00  30 f7 00 00  00 00 00 00  00 00 30 f6   ....0.........0.
0080:   04 00 00 00  00 00 00 00  80 52 00 00  00 00 00 00   .........R......
0090:   00 90 30 f8  08 00 00 00  00 00 00 00  30 f9 01 00   ..0.........0...
00a0:   00 00 00 00  00 00 63 00  62 66 70 83  00 00 00 00   ......c.bfp.....
00b0:   00 00 00 50  a7 00 00 00  00 00 00 00  00 60 a0 60   ...P.........`.`
00c0:   87 61 96 74  73 00 00 00  00 00 00 00  90            .a.ts........
```

disassembler
```
> cargo run -- -d /tmp/abc.bin
0x0: .entry 0x0
0x0: Label_1:
0x0: .pos 0
0x0: irmoveq 0x200, %rsp
0xa: call 0x38
0x13: halt
0x14: halt
0x15: halt
0x16: halt
0x17: halt
0x18: .quad 0xd000d000d
0x20: .quad 0xc000c000c0
0x28: .quad 0xb000b000b00
0x30: .quad 0xa000a000a000
0x38: irmoveq 0x18, %rdi
0x42: irmoveq 0x4, %rsi
0x4c: call 0x56
0x55: ret
0x56: irmoveq 0x8, %r8
0x60: irmoveq 0x1, %r9
0x6a: xorq %rax, %rax
0x6c: andq %rsi, %rsi
0x6e: jmp 0x87
0x77: mrmovq (%rdi), %r10
0x81: addq %r10, %rax
0x83: addq %r8, %rdi
0x85: subq %r9, %rsi
0x87: jne 0x77
0x90: ret
0x200: Label_2:
0x200: .pos 200
```
