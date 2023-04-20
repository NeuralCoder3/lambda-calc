# A Lambda-SK self interpreter

In this files, we verify a self interpreter for the SK lambda calculus. 
The idea is based on 
["Functional Bits: Lambda Calculus based
Algorithmic Information Theory" (John Tromp 2022)](https://tromp.github.io/cl/LC.pdf) ([Github Repository](https://github.com/tromp/AIT)).

An SK-expression is encoded as a bit-sequence which can be interpreted using a lambda calculus expression.

- K is encoded as 00
- S is encoded as 01
- Application A B is encoded as 1 followed by the encoding of A followed by the encoding of B

Sequences are encoded using nested tuples:
- `nil` as `λ x y. y`
- `<a,b>` as `λ f. f a b`

Bits are encoded as booleans (functioning as conditionals):
- `0` as `λ x y. x`
- `1` as `λ x y. y`

[0,1,0] becomes ⟨0, ⟨1, ⟨0, nil⟩⟩⟩.

The idea behind the interpreter is to write a continuation passing style function that checks:
- If the first bit is a 0:
  - If the second bit is a 0, then we have a K
  - If the second bit is a 1, then we have an S
- If the first bit is a 1, then we have an application
  - Recursively, interpret the next two expressions and apply them to each other

The full interpreter is:
- `F := Y (λ F C xs. xs (λ a. a F₀ F₁))`
- `F₀ := λ ys. ys (λ b. C (b K S))`
- `F₁ := F (λ A. F (λ B. C (A B)))`

`xs=a::xr` is either `xs=0::(b::tl as ys)` or `xs=1::(encode a ++ encode b ++ tl)`.

The specification of the interpreter is:
- `F₀ ⟨b, xs⟩ ≡ C (b K S) xs`
- `F₁ (encode A ++ encode B ++ encode xs) ≡ C (A B) (encode xs)`
- `F C (encode x ++ encode xs) ≡ C x (encode xs)`

The proofs work as follows:
- F₀: proof by careful reduction
- F₁: proof using the specification of F
- F
  - unfolding lemma
  - F₀/F₁ selection on head
  - F₀ reduction to K, S
  - F reduction on K/S encoding
  - F₁ reduction to application
  - induction on the encoded SK term


