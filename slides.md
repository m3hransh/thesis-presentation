---
title: Verified Priority Queues in LiquidHaskell
info: |
  ## Master's Thesis Presentation
  Verification of Priority Queue Implementations in LiquidHaskell
class: text-center
drawings:
  persist: false
transition: slide-left
mdc: true
fonts:
  sans: Inter
  serif: Robot Slab
  mono: Fira Code
level: 3
---

# Verified Priority Queues in LiquidHaskell

## Mehran Shahidi

Supervised by

### Prof. Dr. Ralf Hinze

<div class="abs-br m-6 text-xl">
  <button @click="$slidev.nav.openInEditor" title="Open in Editor" class="slidev-icon-btn">
    <carbon:edit />
  </button>
  <a href="https://github.com/m3hransh/pq_verification/" target="_blank" class="slidev-icon-btn">
    <carbon:logo-github />
  </a>
</div>

<style>
h1 {
  background-color:rgba(184, 39, 175, 0.71);
  background-image: linear-gradient(45deg, #4EC5D4 10%,rgb(99, 7, 111) 50%);
  background-size: 100%;
  -webkit-background-clip: text;
  -moz-background-clip: text;
  -webkit-text-fill-color: transparent;
  -moz-text-fill-color: transparent;
}
</style>

---
transition: fade-out
class: text-xl
level: 3
---

# Motivation

### **Program verification** is the process of proving that a program adheres to its intended specifications

<br>
<v-click>

### **Data structure verification** is the process of proving that a data structure and its operations always satisfy their intended specifications and invariants.

</v-click>

---
level: 3
---
# Motivation

<div class="grid grid-cols-2 gap-2 items-center  p-5">
    <div>
  <div class="text-3xl">
    “Program testing can be used to show the presence of bugs, but never to show their absence!”
    </div>
    <div class="text-2xl">
   ― Edsger W. Dijkstra
    </div>

  </div>

  <div class="flex justify-center">
    <img src="/images/dijkstra.jpg" class="rounded-lg shadow-lg max-h-80" alt="Edsger W. Dijkstra" />
  </div>
</div>
---
level: 3
---

# Motivation
## Formal Verification

### Coq / Agda → powerful but heavy  
*(new languages, new tooling, high annotation cost)*

<v-click>

- Most real Haskell code never gets verified because devs must switch ecosystems

</v-click>

<v-click>

- Verification feels “separate” from normal programming

</v-click>
<v-click>

- High barrier → low adoption in everyday projects

</v-click>

---
transition: fade-out
class: text-2xl
level: 3
---

# Motivation

### Goal:  
**Verify real Haskell programs *inside* Haskell**

<br>
<br>
<v-click> Our focus -> Data structures -> Priority Queues</v-click>

---
level: 3
---

# Motivation
<img src="/images/haskellvsagda.jpg" class="h-100 mx-auto" />

---
level: 3
---

# Table of content
<Toc   maxDepth='1' mode='sibling'/>

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 1
---

# What is LiquidHaskell?

### Refinement types extend conventional type systems by attaching logical predicates to base types.

<br>

- 🔣 **SMT-Solver** - Leverages SMT-Solvers such as Z3 for automated reasoning
- 📤 **GHC-Plugin** - Integrates with standard Haskell toolchain

<br>

<v-click>
<img src="/images/LH_flow.svg" />
</v-click>
---
level: 1
zoom: 1.2
---

# Refinement type
````md magic-move {lines: true}
```haskell 
lookup :: Int -> [Int] -> Int
lookup 0 (x : _) = x
lookup x (_ : xs) = lookup (x - 1) (xs)
```
```haskell
unsafeLookup :: Int -> [Int] -> Int
unsafeLookup 0 (x : _) = x
unsafeLookup x (_ : xs) = unsafeLookup (x - 1) (xs)
```
```haskell{*|7}
unsafeLookup :: Int -> [Int] -> Int
unsafeLookup 0 (x : _) = x
unsafeLookup x (_ : xs) = unsafeLookup (x - 1) (xs)

lookup :: Int -> [Int] -> Maybe Int
lookup i xs
  | i < 0 || i >= length xs = Nothing
  | otherwise = Just (unsafe i xs)
```
```haskell{1}
lookup :: Int -> [Int] -> Int
lookup 0 (x : _) = x
lookup x (_ : xs) = lookup (x - 1) (xs)
```
```haskell{1}
{-@ lookup :: i : Nat -> { xs : [a] | i < len xs} -> a @-}
lookup :: Int -> [Int] -> Int
lookup 0 (x : _) = x
lookup x (_ : xs) = lookup (x - 1) (xs)
```
```haskell{1|2-12|11-12}
lookupExample = lookup 2 [10, 21]
>> VV : {v : [GHC.Types.Int] | v == GHC.Types.: (GHC.Types.I# 10) 
  (GHC.Types.: (GHC.Types.I# 21) GHC.Types.[])
  && head v == GHC.Types.I# 10
  && len v == 1 + len (GHC.Types.: (GHC.Types.I# 21) GHC.Types.[])
  && lqdc##$select##GHC.Types.:##1 v == GHC.Types.I# 10
  && lqdc##$select##GHC.Types.:##2 v == GHC.Types.: (GHC.Types.I# 21) GHC.Types.[]
  && tail v == GHC.Types.: (GHC.Types.I# 21) GHC.Types.[]
  && len v >= 0}
    .
    is not a subtype of the required type
      VV : {VV##15150 : [GHC.Types.Int] | GHC.Types.I# 2 < len VV##15150}
```
````
<br>
<img v-click="[5, 6]" src="/images/refinement.svg" class="max-h-20 mx-auto" />

---
level: 3
zoom: 1.3
---
# Refinement type
## Increasing list

````md magic-move {lines: true}
```haskell 
data IncList a 
    = Emp 
    | a :< IncList a
```
```haskell
{-@ data IncList a 
    = Emp 
    | (:<) { hd :: a, tl :: IncList {v : a | hd <= v}} @-}
```
````

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

# Priority Queue Interface

Priority queues are multisets with efficient access to minimum element

````md magic-move {lines: true}
```haskell
class PriorityQueue pq where
  empty    :: (Ord a) => pq a
  isEmpty  :: (Ord a) => pq a -> Bool
  insert   :: (Ord a) => a -> pq a -> pq a
  merge    :: (Ord a) => pq a -> pq a -> pq a
  findMin  :: (Ord a) => pq a -> Maybe a
  splitMin :: (Ord a) => pq a -> MinView pq a
```
```haskell {*|9-13}
class PriorityQueue pq where
  empty    :: (Ord a) => pq a
  isEmpty  :: (Ord a) => pq a -> Bool
  insert   :: (Ord a) => a -> pq a -> pq a
  merge    :: (Ord a) => pq a -> pq a -> pq a
  findMin  :: (Ord a) => pq a -> Maybe a
  splitMin :: (Ord a) => pq a -> MinView pq a

data MinView q a
  = EmptyView 
  | Min { minValue :: a, restHeap :: q a }
```
````

<br>

<v-click>

**Two Implementations:**
1. **Leftist Heaps** - Simple binary tree with rank invariant
2. **Binomial Heaps** - Compositional structure with three layers

</v-click>

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

# Leftist Heap Structure

<div class="grid grid-cols-[4fr_3fr] gap-6 items-center">
<div>

**Invariants**
1. **Heap Property**: `value ≤ all children` 
2. **Leftist Property**: 
`rank(right) ≤ rank(left)` 
3. **Rank Definition**: `rank = 1 + rank(right)`

</div>

<div>
   <img src="/images/LeftistHeap.svg" />
</div>

</div>

---
level: 2
---

# Leftist Heap Implementation




````md magic-move {lines: true}
```haskell
data LeftistHeap a 
  = EmptyHeap
  | HeapNode { value :: a
             , left  :: LeftistHeap a
             , right :: LeftistHeap a
             , rank  :: Int
             }
```
```haskell {*|4}
{-@ data LeftistHeap a = EmptyHeap
  | HeapNode 
    { value :: a
    , left  :: LeftistHeapBound a value
    , right :: {v:LeftistHeapBound a value | rrank v <= rrank left}
    , rank  :: {r:Nat | r == 1 + rrank right}
    }
@-}
```
```haskell {10-14}
{-@ data LeftistHeap a = EmptyHeap
  | HeapNode 
    { value :: a
    , left  :: LeftistHeapBound a value
    , right :: {v:LeftistHeapBound a value | rrank v <= rrank left}
    , rank  :: {r:Nat | r == 1 + rrank right}
    }
@-}

{-@ type LeftistHeapBound a X = { h : LeftistHeap a | isLowerBound X h} @-}
{-@ reflect isLowerBound @-}
isLowerBound :: (Ord a) => a -> LeftistHeap a -> Bool
isLowerBound _ EmptyHeap = True
isLowerBound v (HeapNode x l r _) = v <= x && isLowerBound v l && isLowerBound v r
```
```haskell {5|6}
{-@ data LeftistHeap a = EmptyHeap
  | HeapNode 
    { value :: a
    , left  :: LeftistHeapBound a value
    , right :: {v : LeftistHeapBound a value | rrank v <= rrank left}
    , rank  :: {r:Nat | r == 1 + rrank right}
    }
@-}
```
````
1. **Heap Property**: `value ≤ all children` 
2. **Leftist Property**: 
`rank(right) ≤ rank(left)` 
3. **Rank Definition**: `rank = 1 + rank(right)`

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

# Measures and Reflection

**Measures** project data structures into the logic:

````md magic-move {lines: true}
```haskell
-- Size measure for termination
{-@ measure size @-}
{-@ size :: LeftistHeap a -> Nat @-}
size :: LeftistHeap a -> Int
size EmptyHeap = 0
size (HeapNode _ l r _) = 1 + size l + size r
```
```haskell {*|8-12}
-- Size measure for termination
{-@ measure size @-}
{-@ size :: LeftistHeap a -> Nat @-}
size :: LeftistHeap a -> Int
size EmptyHeap = 0
size (HeapNode _ l r _) = 1 + size l + size r

-- Bag (multiset) to track elements
{-@ reflect bag @-}
bag :: (Ord a) => LeftistHeap a -> Bag a
bag EmptyHeap = B.empty
bag (HeapNode x l r _) = B.put x (B.union (bag l) (bag r))
```
```haskell {*|14-18}
-- Size measure for termination
{-@ measure size @-}
size :: LeftistHeap a -> Int
size EmptyHeap = 0
size (HeapNode _ l r _) = 1 + size l + size r

-- Bag (multiset) to track elements
{-@ reflect bag @-}
bag :: (Ord a) => LeftistHeap a -> Bag a
bag EmptyHeap = B.empty
bag (HeapNode x l r _) = B.put x (B.union (bag l) (bag r))

-- Lower bound predicate  
{-@ reflect isLowerBound @-}
isLowerBound :: (Ord a) => a -> LeftistHeap a -> Bool
isLowerBound _ EmptyHeap = True
isLowerBound v (HeapNode x l r _) = 
  v <= x && isLowerBound v l && isLowerBound v r
```
````

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
layout: section
---
# Verifying Leftist Heap Merge

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

## Heap Merge Implementation



````md magic-move {lines: true}

```haskell
heapMerge :: (Ord a) => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
heapMerge EmptyHeap h2 = h2
heapMerge h1 EmptyHeap = h1
heapMerge h1@(HeapNode x1 l1 r1 _) h2@(HeapNode x2 l2 r2 _)
    | x1 <= x2 = makeHeapNode x1 l1 (heapMerge r1 h2)
    | otherwise = makeHeapNode x2 l2 (heapMerge h1 r2)
```
```haskell{8-13}
heapMerge :: (Ord a) => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
heapMerge EmptyHeap h2 = h2
heapMerge h1 EmptyHeap = h1
heapMerge h1@(HeapNode x1 l1 r1 _) h2@(HeapNode x2 l2 r2 _)
    | x1 <= x2 = makeHeapNode x1 l1 (heapMerge r1 h2)
    | otherwise = makeHeapNode x2 l2 (heapMerge h1 r2)

makeHeapNode :: a -> LeftistHeap a -> LeftistHeap a -> LeftistHeap a
makeHeapNode x h1 h2
    | rrank h1 >= rrank h2 = HeapNode x h1 h2 (rrank h2 + 1)
    | otherwise = HeapNode x h2 h1 (rrank h1 + 1)
```

```haskell{8-11|5-6}
heapMerge :: (Ord a) => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
heapMerge EmptyHeap h2 = h2
heapMerge h1 EmptyHeap = h1
heapMerge h1@(HeapNode x1 l1 r1 _) h2@(HeapNode x2 l2 r2 _)
    | x1 <= x2 = makeHeapNode x1 l1 (heapMerge r1 h2)
    | otherwise = makeHeapNode x2 l2 (heapMerge h1 r2)

makeHeapNode :: x : a
-> {h : LeftistHeap a | isLowerBound x h}
-> {h : LeftistHeap a | isLowerBound x h}
-> {h : LeftistHeap a | isLowerBound x h}
makeHeapNode x h1 h2
    | rrank h1 >= rrank h2 = HeapNode x h1 h2 (rrank h2 + 1)
    | otherwise = HeapNode x h2 h1 (rrank h1 + 1)
```

```haskell {8-11}
heapMerge :: (Ord a) => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
heapMerge EmptyHeap h2 = h2
heapMerge h1 EmptyHeap = h1
heapMerge h1@(HeapNode x1 l1 r1 _) h2@(HeapNode x2 l2 r2 _)
  | x1 <= x2 = makeHeapNode x1 l1 ((heapMerge r1 h2)
  | otherwise = makeHeapNode x2 l2 ((heapMerge h1 r2)

{-@ predicate HeapMergeMin H1 H2 H = 
  ((not (heapIsEmpty H1) && not (heapIsEmpty H2)) => 
    isLowerBound (min (heapFindMin H1) (heapFindMin H2)) H)
@-}
```
```haskell {13-15}
heapMerge :: (Ord a) => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
heapMerge EmptyHeap h2 = h2
heapMerge h1 EmptyHeap = h1
heapMerge h1@(HeapNode x1 l1 r1 _) h2@(HeapNode x2 l2 r2 _)
  | x1 <= x2 = makeHeapNode x1 l1 ((heapMerge r1 h2)
  | otherwise = makeHeapNode x2 l2 ((heapMerge h1 r2)

{-@ predicate HeapMergeMin H1 H2 H = 
  ((not (heapIsEmpty H1) && not (heapIsEmpty H2)) => 
    isLowerBound (min (heapFindMin H1) (heapFindMin H2)) H)
@-}

{-@ predicate BagUnion H1 H2 H = 
  (bag H == B.union (bag H1) (bag H2))
@-}
```
```haskell{1-2}
{-@ heapMerge :: h1:LeftistHeap a -> h2:LeftistHeap a
  -> {h:LeftistHeap a | (HeapMergeMin h1 h2 h) && (BagUnion h1 h2 h)} @-}
heapMerge :: (Ord a) => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
heapMerge EmptyHeap h2 = h2
heapMerge h1 EmptyHeap = h1
heapMerge h1@(HeapNode x1 l1 r1 _) h2@(HeapNode x2 l2 r2 _)
  | x1 <= x2 = makeHeapNode x1 l1 ((heapMerge r1 h2)
  | otherwise = makeHeapNode x2 l2 ((heapMerge h1 r2)
```
```haskell{8-11}
{-@ heapMerge :: h1:LeftistHeap a -> h2:LeftistHeap a
  -> {h:LeftistHeap a | (HeapMergeMin h1 h2 h) && (BagUnion h1 h2 h)} @-}
heapMerge :: (Ord a) => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
heapMerge EmptyHeap h2 = h2
heapMerge h1 EmptyHeap = h1
heapMerge h1@(HeapNode x1 l1 r1 _) h2@(HeapNode x2 l2 r2 _)
  | x1 <= x2 = makeHeapNode x1 l1 ((heapMerge r1 h2)
      `withProof` lemma_merge_case1 x1 x2 r1 h2)
  | otherwise = makeHeapNode x2 l2 ((heapMerge h1 r2)
      `withProof` lemma_merge_case2 x2 x1 r2 h1)
```

```haskell{12-13}
{-@ heapMerge :: h1:LeftistHeap a -> h2:LeftistHeap a
  -> {h:LeftistHeap a | (HeapMergeMin h1 h2 h) && (BagUnion h1 h2 h)} @-}
heapMerge :: (Ord a) => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
heapMerge EmptyHeap h2 = h2
heapMerge h1 EmptyHeap = h1
heapMerge h1@(HeapNode x1 l1 r1 _) h2@(HeapNode x2 l2 r2 _)
  | x1 <= x2 = makeHeapNode x1 l1 ((heapMerge r1 h2)
      `withProof` lemma_merge_case1 x1 x2 r1 h2)
  | otherwise = makeHeapNode x2 l2 ((heapMerge h1 r2)
      `withProof` lemma_merge_case2 x2 x1 r2 h1)

{-@ lemma_merge_case1 :: x1 : a  -> x2 : {a | x1 <= x2}  -> r1 : LeftistHeapBound a x1 
    -> h2 : { LeftistHeapBound a x2 | not (heapIsEmpty h2)} -> {isLowerBound x1 (heapMerge r1 h2)} @-}
```
```haskell{14-23}
{-@ heapMerge :: h1:LeftistHeap a -> h2:LeftistHeap a
  -> {h:LeftistHeap a | (HeapMergeMin h1 h2 h) && (BagUnion h1 h2 h)} @-}
heapMerge :: (Ord a) => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
heapMerge EmptyHeap h2 = h2
heapMerge h1 EmptyHeap = h1
heapMerge h1@(HeapNode x1 l1 r1 _) h2@(HeapNode x2 l2 r2 _)
  | x1 <= x2 = makeHeapNode x1 l1 ((heapMerge r1 h2)
      `withProof` lemma_merge_case1 x1 x2 r1 h2)
  | otherwise = makeHeapNode x2 l2 ((heapMerge h1 r2)
      `withProof` lemma_merge_case2 x2 x1 r2 h1)

{-@ lemma_merge_case1 :: x1 : a  -> x2 : {a | x1 <= x2}  -> r1 : LeftistHeapBound a x1 
    -> h2 : { LeftistHeapBound a x2 | not (heapIsEmpty h2)} -> {isLowerBound x1 (heapMerge r1 h2)} @-}
lemma_merge_case1 x1 x2 EmptyHeap h2    
    = isLowerBound x1 (heapMergeEmptyHeap h2)
    ? lemma_isLowerBound_transitive x1 x2 h2
    *** QED
lemma_merge_case1 x1 x2 r1@(HeapNode _ _ _ _) h2@(HeapNode _ _ _ _) 
    = isLowerBound x1 (heapMerged)
    ? ( lemma_isLowerBound_transitive x1 (min (heapFindMin r1) (heapFindMin h2)) (heapMerged))
    *** QED
        where
            heapMerged = heapMerge r1 h2
```
```haskell{3,15}
{-@ heapMerge :: h1:LeftistHeap a -> h2:LeftistHeap a
    -> {h:LeftistHeap a | (HeapMergeMin h1 h2 h) && (BagUnion h1 h2 h)} 
    / [size r1 , size h2 , 0] @-}
heapMerge :: (Ord a) => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
heapMerge EmptyHeap h2 = h2
heapMerge h1 EmptyHeap = h1
heapMerge h1@(HeapNode x1 l1 r1 _) h2@(HeapNode x2 l2 r2 _)
  | x1 <= x2 = makeHeapNode x1 l1 ((heapMerge r1 h2)
      `withProof` lemma_merge_case1 x1 x2 r1 h2)
  | otherwise = makeHeapNode x2 l2 ((heapMerge h1 r2)
      `withProof` lemma_merge_case2 x2 x1 r2 h1)

{-@ lemma_merge_case1 :: x1 : a  -> x2 : {a | x1 <= x2}  -> r1 : LeftistHeapBound a x1 
    -> h2 : { LeftistHeapBound a x2 | not (heapIsEmpty h2)} -> {isLowerBound x1 (heapMerge r1 h2)} 
    / [size r1 , size h2 , 1] @-} 
lemma_merge_case1 x1 x2 EmptyHeap h2    
    = isLowerBound x1 (heapMergeEmptyHeap h2)
    ? lemma_isLowerBound_transitive x1 x2 h2
    *** QED
lemma_merge_case1 x1 x2 r1@(HeapNode _ _ _ _) h2@(HeapNode _ _ _ _) 
    = isLowerBound x1 (heapMerged)
    ? ( lemma_isLowerBound_transitive x1 (min (heapFindMin r1) (heapFindMin h2)) (heapMerged))
    *** QED
        where
            heapMerged = heapMerge r1 h2
```

````
<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

## Proving Lower Bound Transitivity

Core lemma for heap merge verification:

````md magic-move {lines: true}
```haskell
-- If x ≤ y and y is lower bound of h, then x is lower bound of h
{-@ lemma_isLowerBound_transitive :: x:a 
    -> y:{a | x <= y} 
    -> h:{LeftistHeap a | isLowerBound y h}
    -> {isLowerBound x h}
@-}
lemma_isLowerBound_transitive x y EmptyHeap = ()
lemma_isLowerBound_transitive x y (HeapNode z l r _) = 
  lemma_isLowerBound_transitive x y l 
    &&& lemma_isLowerBound_transitive x y r 
    *** QED
```
````

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

## Other Leftist Heap Operations

Insert and splitMin build on merge:

````md magic-move {lines: true}
```haskell
{-@ heapInsert :: x:a -> h1:LeftistHeap a
  -> {h:LeftistHeap a | 
        not (heapIsEmpty h1) => 
          isLowerBound (min x (heapFindMin h1)) h
        && bag h = B.put x (bag h1)}
@-}
heapInsert :: (Ord a) => a -> LeftistHeap a -> LeftistHeap a
heapInsert x h = heapMerge (HeapNode x EmptyHeap EmptyHeap 1) h
```
```haskell {*}
{-@ heapSplit :: h:LeftistHeap a 
  -> {s:MinView LeftistHeap a | 
       (heapIsEmpty h => isEmptyView s) &&
       (not (heapIsEmpty h) => 
          getMinValue s == heapFindMin h &&
          bag h == B.put (getMinValue s) (bag (getRestHeap s)))}
@-}
heapSplit :: (Ord a) => LeftistHeap a -> MinView LeftistHeap a
heapSplit EmptyHeap = EmptyView
heapSplit (HeapNode x l r _) = Min x (heapMerge l r)
```
````

✅ **Result**: All leftist heap operations verified with minimal lemmas!

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
layout: section
---

# Binomial Heaps Verification

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

## Binomial Heap Structure

<div v-click.hide ="1">
<img  src="/images/BinomialHeap.svg" class=" absolute max-h-90 mx-auto" />
</div>
<div v-click="1">
<img  src="/images/BinomialHeap2.svg" class="absolute max-h-90 mx-auto" />
</div>


<div class="absolute text-3xl ml-10 bottom-0" v-click="2">

$$1 \times 2^3 + 0 \times 2 ^2 + 1 \times 2^1 + 1 \times 2^0 = 11$$

</div>

<style>
.katex {
color: #12b886;
}
</style>

---
level: 2
---

# Pennant Structure

<div class="grid grid-cols-[4fr_3fr] gap-6 items-center">
<div>

**Invariants**
1. **Minimum Property**: `root ≤ all children` 
2. **Left-ordering Property**:  `value ≤ left child` 
3. **Perfect Bin Tree**: `height(left) = height(right)`

</div>

<div>
   <img src="/images/Pennant.svg" />
</div>

</div>

---
level: 2
zoom: 1.2
---

## Binomial Heap Implementation

````md magic-move {lines: true}
```haskell
data BinTree a 
    = Empty
    | Bin { value  :: a
        , left   :: BinTreeBound a value
        , right  :: BinTreeHeight a (bheight left)
        , height :: {h:Nat | h == 1 + bheight right}
        }
```
```haskell {*|9-16}
data BinTree a 
    = Empty
    | Bin { value  :: a
        , left   :: BinTreeBound a value
        , right  :: BinTreeHeight a (bheight left)
        , height :: {h:Nat | h == 1 + bheight right}
        }

data Pennant a =
  P { root    :: a
    , pheight :: Nat
    , bin     :: {b:BinTreeBound a root | bheight b + 1 == pheight}
    }
```
```haskell {*}
data BinomialHeap a 
    = Nil
    | Cons { hd :: BinomialBit a
         , tl :: {bs:BinomialHeap a |
                  not (heapIsEmpty bs) =>
                    rank (bhead bs) = rank hd + 1}
         }


data BinomialBit a 
  = Zero { zorder :: Nat }
  | One  { oorder :: Nat
         , pennant :: {p:Pennant a | pheight p == oorder}
         }
```
````

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
zoom: 1.2
---

## Linking Pennants

Merging two equal-rank pennants into rank+1:

````md magic-move {lines: true}
```haskell
{-@ link :: Ord a => 
      t1:Pennant a
   -> t2:{Pennant a | pheight t2 == pheight t1}
   -> {v:Pennant a | pheight v == pheight t1 + 1 
                     && BagUnion t1 t2 v}
@-}
link :: (Ord a) => Pennant a -> Pennant a -> Pennant a
link (P x1 h1 t1) (P x2 h2 t2)
  | x1 <= x2 = P x1 (h1 + 1) (Bin x2 t2 t1 h1)
  | otherwise = P x2 (h1 + 1) (Bin x1 t1 t2 h1)
```
```haskell {9-12|*}
{-@ link :: Ord a => 
      t1:Pennant a
   -> t2:{Pennant a | pheight t2 == pheight t1}
   -> {v:Pennant a | pheight v == pheight t1 + 1 
                     && BagUnion t1 t2 v}
@-}
link :: (Ord a) => Pennant a -> Pennant a -> Pennant a
link (P x1 h1 t1) (P x2 h2 t2)
  | x1 <= x2 = P x1 (h1 + 1) (Bin x2 t2 t1 h1)
       `withProof` lemma_isLowerBound_transitive x1 x2 t2
  | otherwise = P x2 (h1 + 1) (Bin x1 t1 t2 h1)
       `withProof` lemma_isLowerBound_transitive x2 x1 t1
```
````


<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

## Bit-Level Arithmetic

Heap merge as ripple-carry addition:

````md magic-move {lines: true}
```haskell {*|8-15}
-- Bits can be Zero or One (with pennant)
data BinomialBit a 
  = Zero { zorder :: Nat }
  | One  { oorder :: Nat
         , pennant :: {p:Pennant a | pheight p == oorder}
         }

{-@ bSum :: b1:BinomialBit a -> b2:{BinomialBit a | rank b2 == rank b1} 
  -> {b:BinomialBit a | rank b == rank b1}
@-}

{-@ reflect bCarry @-}
{-@ bCarry :: Ord a => b1:BinomialBit a -> b2:{BinomialBit a | rank b2 == rank b1} 
  -> {b:BinomialBit a | rank b == rank b1 + 1}
@-}
```
```haskell

{-@ bSum :: b1:BinomialBit a -> b2 : {BinomialBit a | rank b2 == rank b1} 
  -> {b:BinomialBit a | rank b == rank b1}
@-}

{-@ bCarry :: Ord a => b1 : BinomialBit a -> b2 : {BinomialBit a | rank b2 == rank b1} 
  -> {b:BinomialBit a | rank b == rank b1 + 1}
@-}

{-@ bFullAdder :: b1:BinomialBit a -> b2 : {BinomialBit a | rank b2 == rank b1}
           -> c:{BinomialBit a | rank c == rank b1}
           -> ({s:BinomialBit a | rank s == rank b1}, 
               {co:BinomialBit a | rank co == rank b1 + 1}) -@}
```
```haskell 

addWithCarry :: h1 : BinomialHeap a 
  -> h2 : {BinomialHeap a | (bRank h2 == bRank h1 ||heapIsEmpty h1)|| heapIsEmpty h2}
  -> carry : {BinomialBit a | ((not (heapIsEmpty h1)) => rank carry == bRank h1)
                              && ((not (heapIsEmpty h2)) => rank carry == bRank h2)}
  -> {b : BinomialHeap a | (not (heapIsEmpty b)) => rank (bhead b) == rank carry}
/ [len h1 , len h2]
```
````

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

## Binomial Heap splitMin


````md magic-move {lines: true}
```haskell
{-@ splitMin :: h:{BinomialHeap a | bRank h == 0} -> MinView BinomialHeap a @-}
splitMin :: (Ord a) => BinomialHeap a -> MinView BinomialHeap a
splitMin heap =
  if hasOnlyZeros heap
    then EmptyView
    else case extractMin heap of
      (minPennant, restHeap) ->
        let converted = case minPennant of
              P _ 0 _ -> restHeap
              P _ _ _ -> ...
         in Min (root minPennant) converted
```
```haskell
{-@ splitMin :: h:{BinomialHeap a | bRank h == 0} -> MinView BinomialHeap a @-}
splitMin :: (Ord a) => BinomialHeap a -> MinView BinomialHeap a
splitMin heap =
  if hasOnlyZeros heap
    then EmptyView
    else case extractMin heap of
      (minPennant, restHeap) ->
        let converted = case minPennant of
              P _ 0 _ -> restHeap
              P _ _ _ -> case restHeap of
                Nil -> reverseToBinomialHeap (dismantle (bin minPennant))
                Cons _ _ -> bAdd restHeap (reverseToBinomialHeap (dismantle (bin minPennant)))
         in Min (root minPennant) converted
```
````

**Steps**: 
1. Find minimum pennant (`extractMin`)
2. Dismantle its tree (`dismantle`)
3. Reverse to standard form (`reverseToBinomialHeap`)
4. Merge with rest (`bAdd`)

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

## Dismantling and Reversing

Converting binary tree back to heap for `splitMin`:

````md magic-move {lines: true}
```haskell
data ReversedBinomialHeap a =
    RNil
  | RCons { rhd :: BinomialBit a
          , rtl :: {bs:ReversedBinomialHeap a | not (isRNil bs) =>
                     rank (rbhead bs) = rank rhd - 1}}
```
```haskell {*|7-17}
data ReversedBinomialHeap a =
    RNil
  | RCons { rhd :: BinomialBit a
          , rtl :: {bs:ReversedBinomialHeap a | not (isRNil bs) =>
                     rank (rbhead bs) = rank rhd - 1}}

{-@ dismantle :: Ord a => t:BinTree a -> {rh:ReversedBinomialHeap a | ValidDismantle t rh} @-}
dismantle :: (Ord a) => BinTree a -> ReversedBinomialHeap a
dismantle Empty = RNil
dismantle (Bin m l r h) =
  RCons (One h (P m h l)) (dismantle r)
    `withProof` lemma_rlast_preserved ...
```
```haskell {*|14-19}
data ReversedBinomialHeap a =
    RNil
  | RCons { rhd :: BinomialBit a
          , rtl :: {bs:ReversedBinomialHeap a | not (isRNil bs) =>
                     rank (rbhead bs) = rank rhd - 1}}

{-@ dismantle :: Ord a => t:BinTree a -> {rh:ReversedBinomialHeap a | ValidDismantle t rh} @-}
dismantle :: (Ord a) => BinTree a -> ReversedBinomialHeap a
dismantle Empty = RNil
dismantle (Bin m l r h) =
  RCons (One h (P m h l)) (dismantle r)
    `withProof` lemma_rlast_preserved ...

{-@ reverseToBinomialHeap ::
      rh:{ReversedBinomialHeap a | ReversedEndsAtZero rh}
   -> {h:BinomialHeap a | ValidReversed rh h}
@-}
reverseToBinomialHeap :: ReversedBinomialHeap a -> BinomialHeap a
```
````

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
layout: section
---

# Results and Conclusions

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

## Verification Summary

<br>

<v-clicks>

**Leftist Heaps** ✅ Fully verified


- All operations: `empty`, `insert`, `merge`, `findMin`, `splitMin`
- Key properties: heap invariant, leftist property, multiset preservation
- Proof effort: Minimal lemmas (mostly transitivity)

</v-clicks>

<br>

<v-clicks>

**Binomial Heaps** ⚠️ Partially verified


- Core components: pennants, link, bit operations, dismantle/reverse
- Verified: rank consistency, structural invariants
- Remaining: some helper functions (`padWithZeros`), full bag proofs

</v-clicks>

<br>

---
level: 2
---
## Verification Summary
**Key Techniques Used:**

<v-clicks>

- Refined data types encode invariants by construction
- Intrisitc verification of operations
- Measures and reflection for reasoning
- PLE automates most equational reasoning
- Explicit lemmas only for complex transitivity

</v-clicks>

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

## Strengths of LiquidHaskell

<br>

<v-clicks>

✅ **Stay in Haskell ecosystem** - No language switch, familiar syntax

✅ **Automation** - SMT solver handles most proofs via PLE

✅ **Incremental adoption** - Can verify gradually, module by module

✅ **Type-driven** - Invariants in types catch errors at compile time

✅ **Minimal annotation** - Less verbose than Coq/Agda for many properties

</v-clicks>

<br>
   
<v-clicks>

**Comparison to alternatives:**
- **vs. Coq/Agda**: More automation, less learning curve
- **vs. Dafny**: Stays in functional paradigm, better for FP
- **vs. Testing**: Static guarantees, exhaustive checking

</v-clicks>

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
level: 2
---

## Limitations & Challenges

<br>

<v-clicks>

⚠️ **Type class limitations** - Cannot refine type class methods directly

⚠️ **Error messages** - Can be cryptic when verification fails

⚠️ **SMT solver timeouts** - Complex properties may need manual guidance

⚠️ **Mutual recursion** - Requires careful termination metrics

⚠️ **Learning curve** - Understanding when to add lemmas takes practice

</v-clicks>
<br>

<v-clicks>

**Workarounds:**
- Use concrete functions instead of type classes
- Break complex proofs into smaller lemmas
- Use reflection judiciously
- Leverage community knowledge and examples

</v-clicks>

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>

---
layout: two-cols
---

# Learn More & Questions

<br>

**Thesis & Code:**
- [GitHub Repository](https://github.com/m3hransh/pq_verification)
- Full thesis with all proofs
- Complete verified implementations

<br>

**Resources:**
- [LiquidHaskell Documentation](https://ucsd-progsys.github.io/liquidhaskell/)
- [Updated Tutorial](https://nikivazou.github.io/lh-course/)
- [Z3 SMT Solver](https://z3prover.github.io/)

<br>

**Questions?**

::right::

<div py-20 px-10>

# Thank You!

<br>
<br>

**Special thanks to:**
- Prof. Dr. Ralf Hinze
- LiquidHaskell community
- Reviewers and colleagues

</div>

<div class="absolute bottom-0  right-0 p-10">
{{ $page }}
</div>
