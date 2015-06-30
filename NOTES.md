assume (a : *) ( y : a)
((λ x → x) : a → a) y

assume b : *
((λ x → λ y → x) : (b → b) → a → b → b) (λ x → x) y

let id = (λ a → λ x → x) : Π (a : * ) → a → a

assume (Bool : *) (False : Bool)
id Bool
id Bool False

id Vec Bool Zero

let plus = (λ k → natElim (λ n → Nat → Nat) (λn → n) (λk → λ rec → λ n → Succ (rec n)) k) : Π (v1 : Nat) → Π (v2 : Nat) → Nat
plus 0
plus 1
plus 29 29

let append = (λa → λm → λv → vecElim a (λm → λ v → Π (n:Nat) → Vec a n → Vec a (plus m n)) (λ m → λ v→v) (λm → λv → λ vs → λ rec → λ n → λ w → Cons a (plus m n) v (rec n w)) m v) : Π(a : *) -> Π (m : Nat) -> Π (v : Vec a m) -> Π (n : Nat) -> Π (w : Vec a n) → (Vec a (plus m n))

assume (a : *) (x : a) (y : a)

append a 0 Nil a
append a 1 Cons a 0 x Nil a
append a 2 (Cons a 1 x (Cons a 0 x (Nil a))) 1 (Cons a 0 y (Nil a))

let nE = (fn m -> fn mz -> fn ms -> fn k -> natElim m mz ms k) : pi (m : Nat -> *) -> (m Zero) -> (pi (l : Nat ) -> (m l) -> (m (Succ l))) -> pi (k: Nat) -> (m k)
let vE = (fn a -> fn m -> fn mn -> fn mc -> fn k -> fn xs -> vecElim a m mn mc k xs) : pi (a : * ) -> pi (m : pi (k : Nat) -> Vec a k -> *) -> (m Zero (Nil a)) -> (pi (l : Nat) -> pi (x : a) -> pi (xs : Vec a l) -> (m l xs) -> (m (Succ l) (Cons a l x xs))) -> pi (k : Nat) -> pi (xs : Vec a k) -> (m k xs)
