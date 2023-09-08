## 2.1 Types are higher groupoids

```rzk
#lang rzk-1
```

Induction principle for equality types:

```rzk
#def path-ind
 (A : U)
 (C : (x : A) -> (y : A) -> (x = y) -> U)
  (d : (x : A) -> C x x refl)
  : (x : A) -> (y : A) -> (p : x = y) -> C x y p
  := \ x y p -> idJ( A , x , C x , d x , y , p )
```


#### 2.1.1. Symmetry - Inversion of paths

```rzk
#def path-sym
  (A : U)
  (x y : A)
  : (x = y) -> (y = x)
  := path-ind A (\ x y _ -> y = x) (\ z -> refl) x y
```

#### 2.1.2. Transitivity - Concatenation of paths
```rzk
#def path-concat
 (A : U)
 (x y : A)
  : (x = y) -> (z : A) -> (y = z) -> (x = z)
  := \p -> path-ind A 
      (\x y p -> ((z : A) -> (y = z) -> (x = z)))
      (\ x z q -> path-ind A
        (\x z q -> (x = z))
        (\x -> refl)
        x z q
      )
      x y p
```

#### 2.1.4.
*Coherence laws on operations of inversion and concatenation*
##### (i) - composition with refl
```rzk
#def concat-refl
  (A : U)
  (x y : A)
  (p : x = y)
  : p = path-concat A x y y p refl
  := path-ind A
    (\ x y p -> p = path-concat A x y y p refl)
    (\ _ -> refl)
    x y p

#def refl-concat
  (A : U)
  (x y : A)
  (p : x = y)
  : p = path-concat A x x y refl p
  := path-ind A
    (\ x y p -> p = path-concat A x x y refl p)
    (\ _ -> refl)
    x y p
```

##### (ii) - composition with inverse
```rzk    
#def inverse-l
  (A : U)
  (x y : A)
  (p : x = y)
  : path-concat A y x y (path-sym A x y p) p  = refl
  := path-ind A
     (\ x y p -> path-concat A y x y (path-sym A x y p) p  = refl )
     (\ _ -> refl)
      x y p
 
#def inverse-r
  (A : U)
  (x y : A)
  (p : x = y)
  : path-concat A x y x p (path-sym A x y p) = refl
  := path-ind A
     (\ x y p -> path-concat A x y x p (path-sym A x y p) = refl )
     (\ _ -> refl)
      x y p
```

##### (iii) - inverse of inverse
```rzk
#def inverse-twice
  (A : U)
  (x y : A)
  (p : x = y)
  : path-sym A y x (path-sym A x y p) = p
  := path-ind A
     (\ x y p -> path-sym A y x (path-sym A x y p) = p )
     (\ _ -> refl)
      x y p
```
##### (iv) - associativity of concatenation
```rzk    
#def concat-assoc'
  (A : U)
  (x y : A)
  (p : x = y)
  : (z : A) -> (q : y = z) -> (w : A) -> (r : z = w) ->
  	path-concat A x y w p (path-concat A y z w q r) = 
      path-concat A x z w (path-concat A x y z p q) r 
  := path-ind 
      A
      (\ x y p -> (z : A) -> (q : y = z) -> (w : A) -> (r : z = w) ->
        path-concat A x y w p (path-concat A y z w q r) = 
          path-concat A x z w (path-concat A x y z p q) r )
			(\x z q w r -> refl)
      x y p
          
#def concat-assoc
  (A : U)
  (x y : A)
  (p : x = y)
  : (z : A) -> (q : y = z) -> (w : A) -> (r : z = w) ->
  	path-concat A x y w p (path-concat A y z w q r) = 
      path-concat A x z w (path-concat A x y z p q) r 
  := path-ind 
      A
      (\ x y p -> (z : A) -> (q : y = z) -> (w : A) -> (r : z = w) ->
        path-concat A x y w p (path-concat A y z w q r) = 
          path-concat A x z w (path-concat A x y z p q) r )
			(\x z q -> path-ind A
          (\x z q -> (w : A) -> (r : z = w) -> path-concat A x z w q r = path-concat A x z w q r)
          (\x w r -> path-ind A
            (\x w r -> r = r)
            (\x -> refl)
            x w r)
          x z q) 
      x y p
              
```