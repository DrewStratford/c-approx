#!

dist/build/CComp/CComp $1 > $1.asm && nasm -f elf32 -F dwarf $1.asm && gcc -m32 $1.o
