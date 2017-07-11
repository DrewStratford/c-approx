#!/bin/bash

asmfile="$(mktemp)"
objectfile="$(mktemp)"
#dist/build/CComp/CComp $1 > $1.asm && nasm -f elf32 -F dwarf $1.asm && gcc -m32 $1.o
if dist/build/CComp/CComp $1 > $asmfile
  then nasm -f elf32 -F dwarf $asmfile -o $objectfile && gcc -m32 $objectfile
  else echo "compilation failed"
fi

rm -f $asmfile
rm -f $objectfile
