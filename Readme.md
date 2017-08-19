# C~

A toy language/compiler that approximates C.

---

## Features

	* int and boolean type
	* basic operators (\*+-/% && || == < >)
	* pointers (called references)
	* control flow (if else, while loops)
	* structures

## To be implemented

	* arrays
	* proper dereferencing of pointers to structs (can only dereference whole struct not just single field)
	* module/header system
	* void/void function calls
	* for loops

## Example

	struct test {
		int a,
		int b
		}
	
	struct test testadd(struct test x, struct test y){
	       return { a : x[a] + y[a], b: x[b] + y[b] };
	}
	
	int main(){
		//note: struct variables must be initialised at declaration
		struct test foo = { a :20 , b : 33 };
		struct test bar = testadd(foo, {a : 30, b : 250});
	
		//note: all function results must be assigned to a variable, even IO.
		int iosink = putChr(bar[a]);
		iosink = putChr(bar[b]);
		
		return 0;
	}

## Compiling/running

The compiler is written in Haskell so requires a recent version of GHC. The compiler itself
emits 32 bit NASM files so you'll need to have NASM and a version of version of GCC capable
of linking 32bit executables. Cabal is reccomended to build the compiler. Be warned this
has only ever been compiled on linux.

### building

	git clone https://github.com/DrewStratford/c-approx.git
	cd c-approx
	cabal build

### compiling a program

There should be a script in c-approx called run.sh which compiles and links the programs.
use like so (in c-approx):

	./run.sh test.prog
	./a.out #run output

run.sh will either report compilation errors or create an executable called a.out
