signature STACK =
sig
    type 'a Stack

    val empty : 'a Stack
    val isEmpty : 'a Stack -> bool
                                  
    val cons : 'a * 'a Stack -> 'a Stack
    val head : 'a Stack -> 'a (* raises Empty if stack is empty *)
    val tail : 'a Stack -> 'a Stack (* raises Empty if stack is empty *)
end

structure List : STACK =
struct
type 'a Stack = 'a list
                   
val empty = []
fun isEmpty s = null s

fun cons (x, s) = x :: s
fun head s = hd s
fun tail s = tl s
end

structure CustomStack : STACK =
struct
datatype 'a Stack = Nil | Cons of 'a * 'a Stack

val empty = Nil
fun isEmpty Nil = true | isEmpty _ = false

fun cons (x, s) = Cons (x, s)
fun head Nil = raise Empty
  | head (Cons (x, s)) = x
fun tail Nil = raise Empty
  | tail (Cons (x, s)) = s
end

    
(* Exercise 2.1
 * Write a function suffixes of type 'a list -> 'a list list that takes
 * a list xs and returns a list of all the suffixes of xs in decreasing
 * order of length. For example,
 *   suffixes [1,2,3,4] = [[1,2,3,4], [2,3,4], [3,4], [4], []]
 * Show that the resulting list of suffixes can be generated in O(n)
 * time and represented in O(n) space.
 *)

fun suffixes [] = [[]]
  | suffixes xs = xs :: suffixes (tl xs)

signature SET =
sig
    type Elem
    type Set

    val empty : Set
    val insert : Elem * Set -> Set
    val member : Elem * Set -> bool
end

signature ORDERED =
(* a totally ordered type and its comparison functions *)
sig
    type T

    val eq : T * T -> bool
    val lt : T * T -> bool
    val leq : T * T -> bool
end

functor UnbalancedSet (Element : ORDERED) : SET =
struct
type Elem = Element.T
datatype Tree = E | T of Tree * Elem * Tree
type Set = Tree
exception Exists
              
val empty = E

(* Exercise 2.2
 * In the worst case, member performs approximately 2d comparisons,
 * where d is the depth of the tree. Rewrite member to take no more
 * than d + 1 comparisons by keeping track of a candidate that might
 * be equal to the query element (say, the last element for which <
 * returned false or <= returned true) and checking the equality only
 * when you hit the bottom of the tree.
 *)

fun member (x, E) = false
  | member (x, s as T (a, y, b)) =
    let fun member2 (x, E, c) = Element.eq (x, c)
          | member2 (x, T (a, y, b), c) =
            if Element.lt (x, y) then member2 (x, a, c)
            else member2 (x, b, y)
    in
        member2 (x, s, y)
    end

(* Exercise 2.3
 * Inserting an existing element into a binary search tree copies the
 * entire search path even though the copied nodes are indistinguishable
 * from the originals. Rewrite insert using exceptions to avoid this
 * copying. Establish only one handler per insertion rather than one
 * handler per iteration.
 *
 * Exercise 2.4
 * Combine the ideas from the previous two exercises to obtain a version
 * of insert that performs no unnecessary copying and uses no more than
 * d + 1 comparisons.
 *)
        
fun insert (x, E) = T (E, x, E)
  | insert (x, s as T (a, y, b)) = 
    let fun insert2 (x, E, c) =
          if Element.eq (x, c) then raise Exists else T (E, x, E)
          | insert2 (x, s as T (a, y, b), c) =
            if Element.lt (x, y) then T (insert2 (x, a, c), y, b)
            else T (a, y, insert2 (x, b, y))
    in
        insert2 (x, s, y)
    end
    handle Exists => s
end

structure OrderedInt : ORDERED =
struct
type T = int
             
fun eq (x, y) = x = y
fun lt (x, y) = x < y
fun leq (x, y) = x <= y
end

structure UnbalancedIntSet = UnbalancedSet(OrderedInt)

(* Exercise 2.5
 * Sharing can also be useful within a single object, not just between
 * objects. For example, if the two subtrees of a given node are
 * identical, then they can be represented by the same tree.
 *   (a) Using this idea, write a function complete : Elem * int -> Tree
 *       where complete (x, d) creates a complete binary tree of depth d
 *       with x stored in every node. (Of course, this function makes no
 *       sense for the set abstraction, but it can be useful as an
 *       auxiliary  function for other abstractions, such as bags.) This
 *       function should run in O(d) time.
 *   (b) Extend this function to create balanced trees of arbitrary size.
 *       These trees will not always be complete binary trees, but should
 *       be as balanced as possible: for any given node, the two subtrees
 *       should differ in size by at most one. This function should run in
 *       O(log n) time. (Hint: use a helper function create2 that, given
 *       a size m, creates a pair of trees, one of size m and one of size
 *       m + 1.)
 *)
                                          
type Elem = OrderedInt.T
datatype Tree = E | T of Tree * Elem * Tree
                                           
fun complete (x, 0) = T (E, x, E)
  | complete (x, n) = let val s = complete (x, n - 1) in T(s, x, s) end

fun balanced (x, 0) = E
  | balanced (x, n) =
    let fun create2 m = (balanced (x, m), balanced (x, m + 1))
        val m = floor ((Real.fromInt n) / 2.0)
    in
        if n mod 2 = 0 then
            let val (s, t) = create2 (m - 1) in T(s, x, t) end
        else
            let val s = balanced (x, m) in T(s, x, s) end
    end

(* debugging *)
        
fun printTree t =
  let fun printTree2 (E, d) = print ("E (d=" ^ (Int.toString d) ^ ")\n")
        | printTree2 (T (E, x, E), d) =
          print ((Int.toString x) ^ " (d=" ^ (Int.toString d) ^ ")\n")
        | printTree2 (T (a, x, b), d) =
          (print ((Int.toString x) ^ " (d=" ^ (Int.toString d) ^ ")\n");
           printTree2 (a, d + 1);
           printTree2 (b, d + 1))
  in
      printTree2 (t, 0)
  end
      
(* Exercise 2.6
 * Adapt the UnbalancedSet functor to support finite maps rather than sets.
 *)

signature FINITEMAP =
sig
    type Key
    type 'a Map

    val empty : 'a Map
    val bind : Key * 'a * 'a Map -> 'a Map
    val lookup : Key * 'a Map -> 'a (* raise NotFound if key is not found *)
end
    
functor UnbalancedFiniteMap (Element : ORDERED) : FINITEMAP =
struct
type Key = Element.T
datatype 'a Tree = E | T of 'a Tree * Key * 'a * 'a Tree
type 'a Map = 'a Tree
exception NotFound
              
val empty = E

fun lookup (x, E) = raise NotFound
  | lookup (x, s as T (a, y, v, b)) =
    if Element.lt (x, y) then lookup (x, a)
    else if Element.lt (y, x) then lookup (x, b)
    else v

fun bind (x, v, E) = T (E, x, v, E)
  | bind (x, v, s as T (a, y, u, b)) =
    if Element.lt (x, y) then T (bind (x, v, a), y, u, b)
    else if Element.lt (y, x) then T (a, y, u, bind (x, v, b))
    else T (a, y, v, b)
end

structure OrderedString : ORDERED =
struct
type T = string
             
fun eq (x, y) = String.compare (x, y) = General.EQUAL
fun lt (x, y) = String.compare (x, y) = General.LESS
fun leq (x, y) = String.compare (y, x) = General.GREATER
end

structure Dictionary = UnbalancedFiniteMap(OrderedString)
