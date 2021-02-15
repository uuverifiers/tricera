# TriCera Preprocessor

A clang tool to preprocess C files before feeding them to TriCera.

It has several components which are called sequentially.

## UsedFunctionAndTypeCollector
It tries to find the main function, and follows all function calls from main
(and from the called functions) until a fixed point in order to determine
used functions and types.

## TypedefRemover
Removes all typedefs. If a typedef contains a record declaration, it is
converted to a regular record declaration.
E.g. `typedef struct {...} S;` is converted to `struct S {...};`.

## UnusedDeclCommenter
Removes all unused declarations, which include both function and type
declarations. It uses the results from "UsedFunctionAndTypeCollector".

## TypeCanoniser
Replaces all types with their canonical versions in the source code.
If a type is a typedef type, it is replaced with the completely desugared
(i.e., canonical) type.
E.g. for the typedefs `typedef T1 T2; typedef T2 * T3;`, `T3 * x` is replaced
with `T1 ** x`.

# Requirements
- cmake v3.4.3 or above.
- llvm-11

# Make
The script `mk` is provided which builds the tool as a shared library inside the
build directory.

The tool can also be built as a stand-alone executable by modifying
CMakeLists.txt and TriceraPreprocessorMain.cpp (replace runTool with main).

# Known Issues
- UnusedDeclCommenter will comment out whole lines that the declaration is in. If
  another declaration is in the same line, it will also be commented out. This
  should usually not be an issue if the other declarations are using the same base
  type, because UnusedDeclCommenter only comments out a declaration (except
  function declarations) if the type of that declaration is never seen in the
  program.

  E.g. For `T1 x; T2 y;`, if either T1 or T2 is not a seen type, both declarations
  will be commented out since they are in the same line.

- TypedefRemover comments out some parts of the record declarations using
  C-style `/*...*/` comments. If the commented-out region has nested comments
  this might lead to unparseable output.

# Credit
The tutorial and examples from clang-tutor were really helpful in getting
started with clang::libtooling, and some parts of the code make use of their
project code:
https://github.com/banach-space/clang-tutor
