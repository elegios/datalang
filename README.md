# Datalang

Datalang is an experiment in programming language creation. The language features type inference, type based macros and a C foreign function interface.

## Design ideas

The idea is to provide a practical language with a relatively simple mapping to machine code while still providing various nice-to-have features. The language strongly encourages separation of code with and without side-effects by providing two function types: func and proc. The former is intended to be a proper mathematical function, i.e. given the same inputs it returns the same output, with no side-effects and no modification of the inputs. The latter is intended to perform side-effects and can change or overwrite arguments that are provided as out arguments. 

Datalang has type inference and a strong static type system. It is possible to create new types with the same underlying representation, but that are treated as different by the type system (i.e. Haskell's newtypes). There is a separation in place between code and data: you cannot place methods on objects (funcs and procs are first class though). You can instead provide purely functional access macros. Example:

```
type Slice[t,n] {
  [i]                 // expressions of the form slice[i]
  | 0 <= i && i < len // panic at run time if index is out of bounds
  -> ptr[i]           // replace slice[i] with slice.ptr[i]
  
  [start=0 :: end=len]                      // expressions of the form slice[s::e], slice[::e], slice[s::], slice[::]
  | 0 <= start && start <= end && end < len // ensure the slice is properly formed at run time
  -> {ref(ptr[start]), end-start} to Slice  // replace slice[s::e] (etc...) with a slice from s (inclusive) to e(exclusive)
} {ptr : $t, len : n}
```

This means that each type knows how to access its contents, but cannot mutate itself, which clarifies where mutation happens to simplify reasoning. Some interesting patterns fall out of this, for example a foreach loop can be written:

```
type Slice[t,n] {
  // as before
  
  ['iter] -> 0
  ['isIter n] -> 0 <= n && n < len
  ['next n] | 0 <= n && n < len -> n+1
  ['fromIter n] | 0 <= n && n < len -> ptr[n]
} {ptr : $t, len : n}

// double each element of slice
let mut it = slice['iter]
while slice['isIter it] {
  defer it = slice['next it]
  slice['fromIter it] *= slice['fromIter it]
}
```

That looks a bit messy though, but with macros (not implemented yet) it could be rewritten as:

```
foreach it in slice {
  it *= it
}
```

This enables many useful control structures to be implemented entirely outside of the compiler.

## Building

...is somewhat tricky at the moment. Assuming you have already built llvm 3.4 and has it installed systemwide you should be able to do:

 1. ```git clone git@github.com:elegios/datalang.git```
 1. ```cd datalang```
 1. ```cabal sandbox init```
 1. ```cabal configure```
 1. ```cabal install --only-dependencies```
 1. ```cabal build```
 
If llvm is installed somewhere else step 5 needs to expose the bin directory of llvm, i.e. ```PATH=/path/to/llvm/bin cabal install --only-dependencies```. After that it should be possible to run ```cabal run testproject/main``` to generate an object file. To actually get a runnable result the system linker needs to be invoked to link any libraries the program depends on, as well as the object, into an actual executable (```testproject/main``` requires the C standard library and [termbox](https://github.com/nsf/termbox)).

At present it is only possible to call C functions on x86_64.

## Future

The language is currently being rewritten in a (for the moment) private branch to have a more lisp-like syntax. This is intended to make the syntax more regular, which simplifies the creation of macros, which is the next feature intended to be added to the language. The macros are intended to utilize the JIT functionality of LLVM to be actual code written the same language, running at compile time.
