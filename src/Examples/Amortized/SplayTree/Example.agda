{-# OPTIONS --rewriting #-}

module Examples.Amortized.SplayTree.Example where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid renaming (_+_ to _⊕_)

open import Calf costMonoid 
open import Calf.Data.List hiding (find)
open import Calf.Data.Nat 
open import Calf.Data.Bool as Bool using (bool; true; false)
open import Calf.Data.Product

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Examples.Amortized.SplayTree.Base
open import Examples.Amortized.SplayTree.SplayTree 

{- 
We will start with a tree that is just a left spine: 

                    6
                   /
                  5
                 /
                4
               /
              3
             /
            2
           /
          1
         /
        0
-} 
spine = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []

{-
 The first splay operation accesses 0, which should rotate 0 to the root.
-}
exampleTree₁ : cmp (F (bool ×⁺ SplayTree .BST.T))
exampleTree₁ = 
    bind (F _) (SplayTree .BST.fromList spine) λ t → 
    SplayTree .BST.find t 0

{- 
  Since 0 is in the tree, it should return true.
  The resulting tree should look like this:
                    0
                     \
                      5
                     / \
                    3   6
                   / \
                  1   4
                   \
                    2
  The cumulative cost of this operation is 3: three double rotations.
-} 
exampleTree₁/result : cmp (F (bool ×⁺ SplayTree .BST.T))
exampleTree₁/result = 
    step (F _) 3 (ret (true , 
        node 
            leaf 
            0 
            (node 
                (node 
                    (node 
                        leaf 
                        1 
                        (node 
                            leaf 
                            2 
                            leaf
                        )
                    ) 
                    3 
                    (node 
                        leaf 
                        4 
                        leaf
                    )
                ) 
                5 
                (node 
                    leaf 
                    6 
                    leaf
                )
            )
    )) 

exampleTree₁/correct : exampleTree₁ ≡ exampleTree₁/result
exampleTree₁/correct = refl

{- 
  The second splay operation accesses 3, which should rotate 3 to the root.
-} 
exampleTree₂ : cmp (F (bool ×⁺ SplayTree .BST.T))
exampleTree₂ =
    bind (F _) (SplayTree .BST.fromList spine) λ t → 
    bind (F _) (SplayTree .BST.find t 0) λ (_ , t) →
    SplayTree .BST.find t 3

{-
    Since 3 is in the tree, it should return true.
    The resulting tree should look like this:
                      3
                     / \
                    /   \ 
                   /     \
                  0       5
                   \     / \
                    1   4   6
                     \
                      2
    The cumulative cost of this operation is 4: one double rotation and 3 from before.
-}
exampleTree₂/result : cmp (F (bool ×⁺ SplayTree .BST.T))
exampleTree₂/result = 
    step (F _) 4 (ret (true , 
        node 
            (node 
                leaf 
                0 
                (node 
                    leaf 
                    1 
                    (node 
                        leaf 
                        2 
                        leaf
                    )
                )
            ) 
            3 
            (node 
                (node 
                    leaf 
                    4 
                    leaf
                ) 
                5 
                (node 
                    leaf 
                    6 
                    leaf
                )
            )
    ))

exampleTree₂/correct : exampleTree₂ ≡ exampleTree₂/result
exampleTree₂/correct = refl

{- 
  The third splay operation accesses 7, which is not in the tree.
-}
exampleTree₃ : cmp (F (bool ×⁺ SplayTree .BST.T))
exampleTree₃ =
    bind (F _) (SplayTree .BST.fromList spine) λ t →
    bind (F _) (SplayTree .BST.find t 0) λ (_ , t) →
    bind (F _) (SplayTree .BST.find t 3) λ (_ , t) →
    SplayTree .BST.find t 7

{-
    Since 7 is not in the tree, it should return false.
    The resulting tree should look unchanged from the previous operation:
                      3
                     / \
                    /   \ 
                   /     \
                  0       5
                   \     / \
                    1   4   6
                     \
                      2
    The cumulative cost of this operation is 4: since no rotations are performed, the cost is the same as before.
-}
exampleTree₃/result : cmp (F (bool ×⁺ SplayTree .BST.T))
exampleTree₃/result = 
    step (F _) 4 (ret (false , 
        node 
            (node 
                leaf 
                0 
                (node 
                    leaf 
                    1 
                    (node 
                        leaf 
                        2 
                        leaf
                    )
                )
            ) 
            3 
            (node 
                (node 
                    leaf 
                    4 
                    leaf
                ) 
                5 
                (node 
                    leaf 
                    6 
                    leaf
                )
            )
    ))

exampleTree₃/correct : exampleTree₃ ≡ exampleTree₃/result
exampleTree₃/correct = refl

{- 
  The fourth splay operation accesses 2, which should rotate 2 to the root.
-}
exampleTree₄ : cmp (F (bool ×⁺ SplayTree .BST.T))
exampleTree₄ =
    bind (F _) (SplayTree .BST.fromList spine) λ t →
    bind (F _) (SplayTree .BST.find t 0) λ (_ , t) →
    bind (F _) (SplayTree .BST.find t 3) λ (_ , t) →
    bind (F _) (SplayTree .BST.find t 7) λ (_ , t) →
    SplayTree .BST.find t 2

{-
    Since 2 is in the tree, it should return true.
    The resulting tree should look like this:
                          2
                         / \
                        /   \ 
                       /     \
                      1       3
                     /         \
                    0           5
                               / \
                              4   6
    The cumulative cost of this operation is 6: one double rotation and one single rotation and 4 from before.
-} 
exampleTree₄/result : cmp (F (bool ×⁺ SplayTree .BST.T))
exampleTree₄/result =
    step (F _) 6 (ret (true , 
        node 
            (node 
                (node 
                    leaf 
                    0 
                    leaf
                ) 
                1 
                leaf
            ) 
            2 
            (node 
                leaf 
                3 
                (node 
                    (node 
                        leaf 
                        4 
                        leaf
                    ) 
                    5 
                    (node 
                        leaf 
                        6 
                        leaf
                    )
                )
            )
    ))

exampleTree₄/correct : exampleTree₄ ≡ exampleTree₄/result
exampleTree₄/correct = refl
