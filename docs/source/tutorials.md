# Tutorials

The repositories relevant to the tutorials can be found [on github](https://github.com/wcqaguxa/agda2hs-examples).

## How to build a small library in agda2hs

[Example source code](https://github.com/wcqaguxa/agda2hs-examples/tree/main/example-basics)

After [installing agda2hs](https://agda.github.io/agda2hs/introduction.html), it's time to write a small library. See the folder example-basics for the files described in this document. 

The minimum required to write a library in Agda2Hs is a top-level folder with at least one `.agda` file and an `.agda-lib` file. In the case of example-basics, it looks like this: 

```
example-basics [project root]
 - HelloWorld.agda
 - example-basics.agda-lib
```

More details about Agda's library management can be found [in the documentation](https://agda.readthedocs.io/en/v2.6.0.1/tools/package-system.html). 

This is how the `example-basics.agda-lib` files looks for our project:

```haskell
name: example-basics
include: .
depend: agda2hs
```
The `include` label specifies the current folder as the path for files to be included in the library. For our toy example it works perfectly, but for a bigger library it might be handy to place all the `.agda` files in a single repository such as `src`.

The only dependency we need so far is `agda2hs`, as that is where `Haskell.Prelude` and agda2hs pragmas live. 

Let's look at the `HelloWorld.agda` file now:

```agda
module HelloWorld where

open import Haskell.Prelude

--defining a type synonym
Entry = Int × List String

--defining a datatype
data Tree (a : Set) : Set where
    Leaf   : a → Tree a
    Branch : a → Tree a → Tree a → Tree a

--agda2hs pragmas
{-# COMPILE AGDA2HS Entry #-}

{-# COMPILE AGDA2HS Tree #-}
```
Let's look at the first line:  
```haskell
module HelloWorld where
```
 Specifying the module name is not strictly necessary for the compilation to work. If missing, the agda2hs compiler will simply take the file name as the module name in Haskell. However, if the file name does not confine to Haskell module naming standards, the resulting Haskell file will be incorrect. Since Agda module naming rules are the same as Haskell's, encapsulating the file in a propely named module is a good practice to create correct Haskell files.
 
```agda
open import Haskell.Prelude
``` 
This part is necessary to access Haskell types used in the type synonym example. 

Next comes the definition of a type synonym and a datatype. However, they are meaningless without the `COMPILE AGDA2HS` pragmas. For every new construct (Entry, Tree in this example), there should be one `{-# COMPILE AGDA2HS <construct-name> #-}` pragma. If the pragma is missing, the relevant agda code will be skipped during compilation. 

In general the pragmas can be placed anywhere in the code after the definition, but it is a good practice to place them just under the relevant definition. If the name is misspelled in the pragma, the compiler will issue a warning but continue proceeding.

### Compilation

To verify our code is correct, you can load the Agda file using `C-c C-l`. In order to compile the file, run `agda2hs HelloWorld.agda` and verify that the haskell file `HelloWorld.hs` works as expected.

## How to manage structure and dependencies of a bigger repository?

[Example source code](https://github.com/wcqaguxa/agda2hs-examples/tree/main/example-structure)

Ideally, a working repository should have more than one file. The repository `example-structure` contains an example of a minimally bigger project, with intuition on how to manage a bigger codebase. 

The source code of agda resides in `/src/agda`, which is reflected in the path included in `example-structure.agda-lib` file: 

```
name: example-structure
include: ./src/agda
depend: agda2hs
```

The `agda` folder contains two files: `Definition.agda`, which contains a declaration of a data type `CountDown` and `Usage.agda`, which contains its constructor. Usually, there is no good reason to split those in two files, but it gives a good opportunity to show how these would interact under `agda2hs`. 

To use the module `Definition` in `Usage.agda`, it has to be imported:
```agda
open import Definition
```
It does not have to be specified for agda2hs to compile this import. If the import is used by any of the compiled code, the relevant Haskell module will be likewise imported in the target file; the irrelevant imports are automatically skipped. 

However, both files need to import `Haskell.Prelude` independently of each other to be able to use it.

### Compilation

In principle, `agda2hs` has to be invoked on file-by-file basis and to define a compilation of a whole folder, additional scripting is neccesary. However, since `Definition` is imported in `Usage`, when compiling the latter, the former also will be compiled as a ncessary dependency. Thus, in our example, it is only necessary to execute `agda2hs` once.

Since the target repository is different than the source, it has to be specified as an argument. An example script, to be executed from the root of `example-structure` is placed in `script.sh`:

```bash
agda2hs ./src/agda/Usage.agda -o ./src/haskell/
```