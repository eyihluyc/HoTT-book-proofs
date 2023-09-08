## 2.1 Functions are functors

```rzk
#lang rzk-1
```

#### 2.2.1.
*application / action on paths*
```rzk
#def ap
	(A B : U)
  (f : A -> B)
	(x y : A)
	(p : x = y)
  : f x = f y
  := path-ind
    A
    (\ x y p -> f x = f y)
    (\x -> refl)
    x y p
```

#### 2.2.2.
*`ap` behaves functorially*

##### (i) - `ap (p · q) = ap (p) · ap (q)`
```rzk      
#def ap-concat
  (A B : U)
  (f : A -> B)
	(x y : A)
	(p : x = y)
  : (z : A) -> (q : y = z) -> ap A B f x z (path-concat A x y z p q) =
    path-concat B (f x) (f y) (f z) (ap A B f x y p) (ap A B f y z q)
  := path-ind
      A
      (\ x y p -> (z : A) -> (q : y = z) -> ap A B f x z (path-concat A x y z p q) =
    			path-concat B (f x) (f y) (f z) (ap A B f x y p) (ap A B f y z q))
      (\ x z q -> refl)
      x y p
 ```
 
 ##### (i) - `ap (inv (p)) = inv (ap (p))`
 ```rzk
#def ap-inverse
  (A B : U)
  (f : A -> B)
	(x y : A)
	(p : x = y)
  : ap A B f y x (path-sym A x y p) =
			path-sym B (f x) (f y) (ap A B f x y p)
  := path-ind
      A
      (\ x y p -> ap A B f y x (path-sym A x y p) = path-sym B (f x) (f y) (ap A B f x y p))
      (\ x -> refl)
      x y p

 ```
 
 ##### (iii) - `ap_g (ap_f (p)) = ap_{f ◦ g} (p)`

 ```rzk      
#def ap-twice
  (A B C : U)
  (f : A -> B)
  (g : B -> C)
	(x y : A)
	(p : x = y)
  : ap B C g (f x) (f y) (ap A B f x y p) =
			ap A C (\ x -> g (f x)) x y p
  := path-ind
      A
      (\ x y p -> ap B C g (f x) (f y) (ap A B f x y p) = ap A C (\ x -> g(f x)) x y p)
      (\ x -> refl)
      x y p
 ```
 
 ##### (iv) - `ap_id`

 ```rzk  
#def ap-id
  (A : U)
	(x y : A)
	(p : x = y)
  : ap A A (\ x -> x) x y p = p
  := path-ind
      A
      (\ x y p -> ap A A (\ x -> x) x y p = p)
      (\ x -> refl)
      x y p
```