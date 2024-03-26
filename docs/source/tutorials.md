# Tutorials

The repositories relevant to the tutorials can be found [on github](https://github.com/wcqaguxa/agda2hs-examples).

## How to build a small library in agda2hs

[Example source code](https://github.com/agda/agda2hs/tree/master/tutorials/example-basics)

After [installing agda2hs](https://agda.github.io/agda2hs/introduction.html), it's time to write a small library. See the folder example-basics for the files described in this document. 

The minimum required to write a library in Agda2Hs is a top-level folder with at least one `.agda` file and an `.agda-lib` file. In the case of example-basics, it looks like this: 

```
example-basics [project root]
 - HelloWorld.agda
 - example-basics.agda-lib
```

More details about Agda's library management can be found [in the documentation](https://agda.readthedocs.io/en/v2.6.0.1/tools/package-system.html). 

This is how the `example-basics.agda-lib` file looks for our project:

```
name: example-basics
include: .
depend: agda2hs
flags: --erasure
```
The `include` label specifies the current folder as the path for files to be included in the library. For our toy example it works perfectly, but for a bigger library it might be handy to place all the `.agda` files in a single repository such as `src`.

The only dependency we need so far is `agda2hs`, as that is where `Haskell.Prelude` and agda2hs pragmas live. 

Finally, to be able to  import modules we need in this example, erasure needs to be enabled. We add it as a flag.

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
 Specifying the module name is not strictly necessary for the compilation to work. If missing, the agda2hs compiler will simply take the file name as the module name in Haskell. However, if the file name does not confine to Haskell module naming standards, the resulting Haskell file will be incorrect. Since Agda module naming rules are the same as Haskell's, encapsulating the file in a properly named module is a good practice to create correct Haskell files.
 
```agda
open import Haskell.Prelude
``` 
This part is necessary to access Haskell types used in the type synonym example. 

Next comes the definition of a type synonym and a datatype. However, they are meaningless without the `COMPILE AGDA2HS` pragmas. For every new construct (Entry, Tree in this example), there should be one `{-# COMPILE AGDA2HS <construct-name> #-}` pragma. If the pragma is missing, the relevant agda code will be skipped during compilation. 

In general the pragmas can be placed anywhere in the code after the definition, but it is a good practice to place them just under the relevant definition. If the name is misspelled in the pragma, the compiler will issue a warning but continue proceeding.

### Compilation

To verify our code is correct, you can load the Agda file using `C-c C-l`. In order to compile the file, run `agda2hs HelloWorld.agda` and verify that the haskell file `HelloWorld.hs` works as expected.

## How to manage structure and dependencies of a bigger repository?

[Example source code](https://github.com/agda/agda2hs/tree/master/tutorials/example-structure)

Ideally, a working repository should have more than one file. The repository `example-structure` contains an example of a minimally bigger project, with intuition on how to manage a bigger codebase. 

The source code of agda resides in `/src/agda`, which is reflected in the path included in `example-structure.agda-lib` file: 

```
name: example-structure
include: ./src/agda
depend: agda2hs
flags: --erasure
```

The `agda` folder contains two files: `Definition.agda`, which contains a declaration of a data type `CountDown` and `Usage.agda`, which contains its constructor. Usually, there is no good reason to split those in two files, but it gives a good opportunity to show how these would interact under `agda2hs`. 

To use the module `Definition` in `Usage.agda`, it has to be imported:
```agda
open import Definition
```
It does not have to be specified for agda2hs to compile this import. If the import is used by any of the compiled code, the relevant Haskell module will be likewise imported in the target file; the irrelevant imports are automatically skipped. 

However, both files need to import `Haskell.Prelude` independently of each other to be able to use it.

### Compilation

In principle, `agda2hs` has to be invoked on file-by-file basis and to define a compilation of a whole folder, additional scripting is necessary. However, since `Definition` is imported in `Usage`, when compiling the latter, the former also will be compiled as it is a dependency. Thus, in our example, it is only necessary to execute `agda2hs` once.

Since the target repository is different than the source, it has to be specified as an argument. An example script, to be executed from the root of `example-structure` is placed in `script.sh`:

```bash
agda2hs ./src/agda/Usage.agda -o ./src/haskell/
```
## How (and what) to prove?

[Example source code](https://github.com/agda/agda2hs/tree/master/tutorials/example-proofs)

This tutorial aims to explain how to apply different formal verification techniques compliant with agda2hs and haskell. 

### Constructor constraints

The code described in this section can be found in the file `Triangle.agda`.

Let's say we want to have a data type describing a triangle. A first attempt might look somewhat like this:

```agda
open import Haskell.Prelude

data Triangle : Set where
    MkTriangle : (alpha beta gamma : Nat)
           → Triangle

{-# COMPILE AGDA2HS Triangle #-}
```
It's defined with three angles, because maybe thats the only property we are interested in so far. However, three arbitrary angle values do not make a triangle. First of all, they cannot be negative - to make things easier we use natural numbers (`Nat`) to represent the angle values. But that is not enough, three angles can constitute a triangle only if they sum up to 180 degrees and at most one angle is right or obtuse. This can be modeled in Agda:

```agda
open import Haskell.Prelude

countBiggerThan : ⦃ Ord a ⦄ → List a → a → Int 
countBiggerThan xs b = length (filter (λ x → (x >= b)) xs)

{-# COMPILE AGDA2HS countBiggerThan #-}

data Triangle : Set where
    MkTriangle : (alpha beta gamma : Nat)
        → ⦃ @0 h₁ : (((alpha + beta + gamma) == 180) ≡ True )⦄
        → @0 ⦃ ((countBiggerThan
     (alpha ∷ beta ∷  gamma ∷ []) 90 <= 1) ≡ True ) ⦄
           → Triangle

{-# COMPILE AGDA2HS Triangle #-}
```
Adding two hypotheses to the type signature of MkTriangle does the trick. 
 Notice the use of double brackets, which signify the use of [instance arguments](https://agda.readthedocs.io/en/latest/language/instance-arguments.html): they allow Agda to infer the hypotheses if they are present in the context, instead of having them manually applied each and every time. 

These hypotheses cannot be compiled to Haskell, therefore they have to be erased. This is done by annotating them with [0-quantity parameters](0-Quantity). To correctly annotate a hypothesis with quantity, it has to be explicitly named: in this case h₁. Alternatively, it can also be applied to the whole bracket, like in the second hypothesis. 

The helper function `countBiggerThan` could also operate solely on natural numbers, but this way it show another example of using instance arguments, which map to Haskell's typeclass constraints.

You might want to ask, what is the point of adding hypotheses if they will be erased in Haskell anyway? If you write the remainder of the code in Haskell, it is indeed the case. However, defining the data type in Agda requires the hypotheses to be present when constructing variables of that type:

```agda
createTriangle : Nat -> Nat -> Nat -> Maybe Triangle
createTriangle alpha beta gamma 
    = if (countBiggerThan (alpha ∷ beta ∷  gamma ∷ []) 90 <= 1)
        then if (alpha + beta + gamma == 180 )
            then Just (MkTriangle alpha beta gamma) 
            else Nothing
        else Nothing

{-# COMPILE AGDA2HS createTriangle #-}
```
Unfortunately, the instance arguments are inferred only if presented in exactly the same shape as hypotheses in the constructor, which is the cause of perceived redundancy of the if-then-else statement - chaining the hypotheses with `&&` (the AND operator defined in `Haskell.Prim.Bool` in Agda2hs) will not allow for the reference to be inferred automatically, and the proofs would have to be provided manually. An example for that can be seen in the alternative `createTriangle₁` function:

```agda
createTriangle₁ : Nat -> Nat -> Nat -> Maybe Triangle
createTriangle₁ alpha beta gamma 
    = if ((countBiggerThan (alpha ∷ beta ∷  gamma ∷ []) 90 <= 1) 
            && (alpha + beta + gamma == 180 )) 
        then (λ ⦃ h₁ ⦄ →  Just (MkTriangle alpha beta gamma 
            ⦃ &&-rightTrue h₁ ⦄ 
            ⦃ &&-leftTrue h₁ ⦄) 
        )
        else Nothing
 
{-# COMPILE AGDA2HS createTriangle₁ #-}

```
While using this alternative function offers much cleaner Haskell code as an output (no nested if statements), however the Agda side gets a bit messier. Two things are worth noting here: first, to be able to operate on the hypothesis asserted in the if condition, the branch has to be rewritten as an anonymous function taking the assertion as instance argument. Secondly, to explicitly provide the instance arguments, it also has to be done inside the double curly brackets. 

Lastly, the two functions used to extract conditions from the compound condition: `&&-rightTrue` and `&&-leftTrue` were defined in `Haskell.Law.Bool`. The `Law` folder contains many theorems useful for designing your own proofs. This will be expanded on in following sections. 

### Function or Predicate?

The code described in this section can be found in the file `Ascending.agda`. 

We will try to define ascending order on lists, which will allow us to use statements about the order in later proofs and programs. 

A first attempt at definition could be a function that can provide judgments on instances of lists:

```agda
isAscending : ⦃ iOrdA : Ord a ⦄ → List a → Bool
isAscending [] = True
isAscending (x ∷ []) = True
isAscending (x ∷ y ∷ xs) = if x <= y then isAscending 
    (y ∷ xs) else False

{-# COMPILE AGDA2HS isAscending #-}
```
This function can be compiled to Haskell without any issue, however, when you try using it in proofs you can notice that it is not the most handy definition: since the different cases are anonymous, invoking them is not straightforward and might require defining more proof cases with additional assertions about the values input data (an example of which can be found [further in the tutorial](function-example)) A better definition might be a predicate, instead:

```agda
data IsAscending₂ {a : Set} ⦃ iOrdA : Ord a ⦄ : List a → Set where
    Empty : IsAscending₂ []
    OneElem : (x : a) →  IsAscending₂ (x ∷ [])
    ManyElem : (x y : a) (xs : List a) 
        → ⦃ IsAscending₂ (y ∷ xs) ⦄
        → ⦃ IsTrue (x <= y) ⦄
        → IsAscending₂ (x ∷ y ∷ xs)
```
This data type cannot be compiled to Haskell, as they do not allow to match on specific values. However, some amount of equivalency can be proven between these two definitions. They are not structurally different (one evaluates to True and the other to a data type), therefore they cannot be equal per the `≡` operator. Instead, there occurs the material equivalence relation (`⇔`), such that if the function returns `True`, the predicate holds, and vice versa. Let's try to prove it then!

The signature of the first direction will look like this:

```agda
proof₁ : ⦃ iOrdA : Ord a ⦄ (xs : List a) → ⦃ IsAscending₂ xs ⦄ 
    → (IsTrue (isAscending xs)) 
proof xs = ?
```

> Note: in Agda, you can use [interactive mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#commands-in-context-of-a-goal) to assist in proofs. Question marks will be loaded to open goals. THis feature doesn't work yet seamlessly with agda2hs but the preview of context and splitting based on cases will guide with both more complicated and trivial proofs. 

Since there are three constructors for the `IsAscending₂` predicate, there need to be only three cases in the proof, two of which are trivial:

```agda
proof₁ : ⦃ iOrdA : Ord a ⦄ (xs : List a) → ⦃ IsAscending₂ xs ⦄ 
    → (IsTrue (isAscending xs)) 
proof₁ [] = IsTrue.itsTrue 
proof₁ (x ∷ []) = IsTrue.itsTrue
proof₁ (x ∷ x₁ ∷ xs) ⦃ (ManyElem .x .x₁ .xs ⦃ h₁ ⦄ ⦃ h₂ ⦄) ⦄ = ?
```
In the third case, we need insight into the `IsAscending₂` predicate so it has to be explicitly invoked. Later in the proof we will only need the h₂ hypothesis, but because its the second implicit argument, both need to be stated. The goal is of the shape `IsTrue (isAscending xs)`, but it cannot be easily constructed. Instead, this goal can be mapped to `isAscending xs ≡ True`, which allows to use [chains of equality](https://plfa.github.io/Equality/#chains-of-equations) syntax - transforming the first statement in the equation step by step until we obtain the second statement in a given equality.

```agda
useEq : {x y : Bool} → x ≡ y → IsTrue x → IsTrue y
useEq {True} {True} eq is = IsTrue.itsTrue

reverseEq : { x : Bool } → (IsTrue x) → x ≡ True
reverseEq {False} ()
reverseEq {True} input = refl 

proof₁ (x ∷ x₁ ∷ xs) ⦃ (ManyElem .x .x₁ .xs ⦃ h₁ ⦄ ⦃ h₂ ⦄) ⦄ = useEq ( sym $
    begin
        isAscending (x ∷ x₁ ∷ xs)
    ≡⟨⟩ 
        (if x <= x₁ then isAscending (x₁ ∷ xs) else False)
    ≡⟨ ifTrueEqThen (x <= x₁)  (reverseEq h₂) ⟩ 
        isAscending (x₁ ∷ xs)
    ≡⟨ reverseEq (proof₁ (x₁ ∷ xs) ) ⟩ 
        True
    ∎ ) IsTrue.itsTrue
```
Two helper functions, useEq and reverseEq, had to be added to easily operate on the goal. Even though both of them have trivial proofs, they need to be stated explicitly so that the proper type signature can be invoked. To inspect other helper functions used in the proof, try loading the source code in agda - the definitions all come from `Haskell.Prelude`. 

The reverse direction of the iff proof is, again, substantially more complicated. First, the necessary helper proofs will be discussed.

```agda
--reductio ad absurdum
absurd₁ : {x : Bool} → (x ≡ True) → (x ≡ False) → ⊥
absurd₁ {False} () b 
absurd₁ {True} a ()
```
Reductio ad absurdum is a necessary tactic for dealing with self-contradictory statements. If such statement is one of the input arguments, this contradiction can be discarded with the [`()` keyword](https://agda.readthedocs.io/en/latest/language/function-definitions.html#absurd-patterns) in place of the contradictory argument. However, if the absurd is arising from some combination of the input arguments, it requires some helper method. 

(function-example)=

```agda
--inductive hypothesis for isAscending function
helper₁ : ⦃ iOrdA : Ord a ⦄ (x : a) (xs : List a) 
    → isAscending xs ≡ False → (isAscending (x ∷ xs)) ≡ False
helper₁ x xs h₁ with (isAscending (x ∷ xs)) in h₂
helper₁ x (x₁ ∷ xs) h₁ | True  with (x <= x₁)
helper₁ x (x₁ ∷ xs) h₁ | True | True = magic (absurd₁ h₂ h₁)
helper₁ x (x₁ ∷ xs) h₁ | True | False = sym h₂
helper₁ x xs h₁ | False = refl
```
Here is a helper method for the inductive hypothesis. Notice that where in the predicate syntax we were able to pattern-match on the different constructor, when working with a function, the only way to narrow down to different cases is to pattern match on the possible values of the function output. The [`with ... in` syntax](https://agda.readthedocs.io/en/latest/language/with-abstraction.html) can be used in such cases. In the first usage of the syntax, the output of the function is needed to be applied in the proof, so it needs to be saved *in* a value to be accessed in the context. This is what applying `in h₂` achieves. In the second usage, Agda manages to simplify the necessary arguments automatically, so it is not necessary to add the assertion to the syntax. 

The applied `absurd₁` function can be given as input argument to the `magic` function to resolve the internal contradiction. `magic` lives in `Haskell.Prim` which also needs to be imported. 

```agda
--proof for (function returns true) → predicate holds
theorem₂ : ⦃ iOrdA : Ord a ⦄ (xs : List a) 
    → (IsTrue (isAscending xs)) → IsAscending₂ xs
theorem₂ [] h₁ = Empty
theorem₂ (x ∷ []) h₁ = OneElem x
theorem₂ (x ∷ x₁ ∷ xs) h₁ with (isAscending xs) in h₂ | (x <= x₁) in h₃
theorem₂ (x ∷ x₁ ∷ xs) h₁ | True  | True = ManyElem x x₁ xs  
    ⦃ theorem₂helper (x₁ ∷ xs) h₁ ⦄ ⦃ useEq ( sym $ h₃ ) IsTrue.itsTrue ⦄
theorem₂ (x ∷ x₁ ∷ xs) ()    | _  | False 
theorem₂ (x ∷ x₁ ∷ xs) h₁ | False | True = magic (
         absurd₁ (reverseEq h₁) (helper₁ x₁ xs h₂) )
```

Finally, the proof can be constructed. The recursive case of the proof had to be split into three different cases, but in the place where one would expect to be able to use `theorem₂` recursively, `theorem₂helper` is used instead: 

```agda
--recursion helper
postulate3
   theorem₂helper : ⦃ iOrdA : Ord a ⦄ (xs : List a) 
        → (IsTrue (isAscending xs)) → IsAscending₂ xs
```

The `theorem₂helper` is a definition of the same type as the actual proof, but without a proof attached - it was only postulated. [Postulates](https://agda.readthedocs.io/en/latest/language/postulates.html) are in general a bad practice. Here it was necessary, as the termination check did not recognize that it is being applied to a recursive case. However, doesn't this invalidate the whole proof? Since postulates are a bad practice, can we do better? Turns out, termination checks on recursive cases [is a known issue when using `with abstraction`](https://agda.readthedocs.io/en/latest/language/with-abstraction.html#termination-checking). Thus, in the next attempt, we can get rid of the postulate:

```agda
helper₂ : ⦃ iOrdA : Ord a ⦄ (x : a) (xs : List a) 
    → (IsTrue (isAscending (x ∷ xs))) → (IsTrue (isAscending xs))
helper₂ x [] h₁ = IsTrue.itsTrue
helper₂ x (x₁ ∷ xs) h₁ with (x <= x₁) in h₂
helper₂ x (x₁ ∷ xs) h₁ | True = h₁
helper₂ x (x₁ ∷ xs) () | False 

--proof for (function returns true) → predicate holds version 2
theorem₃ : ⦃ iOrdA : Ord a ⦄ (xs : List a) 
    → (IsTrue (isAscending xs)) → IsAscending₂ xs
theorem₃ [] h₁ = Empty
theorem₃ (x ∷ []) h₁ = OneElem x
theorem₃ (x ∷ x₁ ∷ xs) h₁ with (theorem₃ (x₁ ∷ xs) (helper₂ x (x₁ ∷ xs) h₁)) 
theorem₃ (x ∷ x₁ ∷ xs) h₁ | _ with (x <= x₁) in h₂ 
theorem₃ (x ∷ x₁ ∷ xs) h₁ | h₃ | True  = ManyElem x x₁ xs 
        ⦃ h₃ ⦄ ⦃ useEq ( sym $ h₂ ) IsTrue.itsTrue ⦄
theorem₃ (x ∷ x₁ ∷ xs) () | _  | False 
```
We need another helper function to obtain the correct hypothesis about the tail of the list, but thanks to this approach we can remove one of the assertions about the input values. On the other hand, we need to break up the single `with` assertion into two different lines - if both the new recursive hypothesis (`h₃`) and `h₂` were defined in the same step, Agda wouldn't be able to implicitly apply `h₂` in the `h₁` hypothesis and reason about it being a contradiction in the last case. This way, we finally obtain a correct proof. 

With these proofs, the differences between using these two different styles of describing properties of the code are clear, and some basic principles of building proofs were demonstrated. 

From all the functions and data types discussed, only the first can be compiled into Haskell. The predicate type class and the proofs cannot be compiled as they use concepts that are not supported by Haskell or agda2hs. However, they shouldn't be compiled; they should remain on the "Agda side" as the formal verification of the written code. 
