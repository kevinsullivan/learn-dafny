// Here's a method that illustrates boolean operators in Dafny
method BoolOps() returns (r: bool)
{
    var t: bool := true;
    var f := false;
    var not := !t;
    var conj := t && f;     // short-circuiting
    var disj := t || f;     // short-circuiting
    var impl := t ==> f;    // right associative, s.c. from left
    var foll := t <== f;    // left associative, s.c. from right
    var equv := t <==> t;
    return true;
 }
/* Methods aren't required to return results. Such methods
   do their jobs by having side effects, e.g., doing output
   or writing data into global variables (usually a bad idea).
   Here's a method that doesn't return a value. It illustrates
   numerical types, syntax, and operations.
*/
method NumOps()
{
    var r1: real := 1000000.0;
    var i1: int := 1000000;
    var i2: int := 1_000_000;   // underscores for readiability
    var i3 := 1_000;            // Dafny can often infer types
    var b1 := (10 < 20) && (20 <= 30); // a boolean expression
    var b2 := 10 < 20 <= 30;    // equivalent, with "chaining"
    var i4: int := (5.5).Floor; // 5
    var i5 := (-2.5).Floor;     // -3
    var i6 := -2.5.Floor;        // -2 = -(2.5.Floor); binding!
}

// Characters (char) are handled sort of as they are in C, etc.
method CharFun()
{
    var c1: char := 'a';
    var c2 := 'b';
    // var i1 := c2 - c1;
    var i1 := (c2 as int) - (c1 as int);    // type conversion
    var b1 := c1 < c2;  // ordering operators defined for char
    var c3 := '\n';     // c-style escape for non-printing chars
    var c4 := '\u265B'; // unicode, hex, "chess king" character
}

// Polymorphic finite and infinite set types.
// set<T> and iset<T>. T must support equality.
method SetPlay()
{
    var empty: set<int> := {};
    var primes := {2, 3, 5, 7, 11};
    var squares := {1, 4, 9, 16, 25};
    var b1 := empty < primes;    // strict subset
    var b2 := primes <= primes;   // subset
    var b3: bool := primes !! squares; // disjoint
    var union := primes + squares;
    var intersection := primes * squares; //intersection
    var difference := primes - {3, 5};
    var b4 := primes == squares;    // false
    var i1 := | primes |;   // cardinality (5)
    var b5 := 4 in primes;  // membership (false)
    var b6 := 4 !in primes; // non-membership
    /*
     we'll come back to infinite sets and
     set comprehension notations later on
    */
}

// Polymorphic sequences (often called "lists").
// A function from indices to values. Some of 
// the operations require that T support equality.
method SequencePlay()
{
    var empty_seq: seq<char> := [];
    var hi_seq: seq<char> := ['h', 'i'];
    var b1 := hi_seq == empty_seq; // equality; !=
    var hchar := hi_seq[0];        // indexing 
    var b2 := ['h'] < hi_seq;   // proper prefix
    var b3 := hi_seq < hi_seq;  // this is false
    var b4 := hi_seq <= hi_seq; // prefix, true
    var sum := hi_seq + hi_seq; // concatenation
    var len := | hi_seq |;
    var Hi_seq := hi_seq[0 := 'H']; // update
    var b5 := 'h' in hi_seq; // member, true, !in
    var s := [0,1,2,3,4,5];
    var s1 := s[0..2];  // subseqence
    var s2 := s[1..];   // "drop" prefix of len 1
    var s3 := s[..2];   // "take" prefix of len 2
    // there's a slice operator, too; later
 }

 /*
    Dafny has strings. Strings are literally just
    sequences of characters (of type seq<char>), so
    you can use all the sequence operations on strings.
    Dafny provides additional helpful syntax for strings.
*/
method StringPlay() 
 {
     var s1: string := "Hello CS2102!";
     var s2 := "Hello CS2102!\n";   // return
     var s3 := "\"Hello CS2102!\""; // quotes
 }

/*
  Dafny also supports polymorphic maps, both 
  finite (map<K,V>) and infinite (imap<K,V>).
  The key type, K, must support equality (==).
  In mathematical terms, a map really represents
  a binary relation, i.e., a set of <K,V> pairs,
  which is to say a subset of the product set,
  K * V, where we view the types K and V as
  defining sets of values.
  */
method MapPlay()
{
    // A map literal is keyword map + a list of maplets.
    // A maplet is just a single <K,V> pair (or "tuple").
    // Here's an empty map from strings to ints
    var emptyMap: map<string,int> := map[];

    // Here's non empty map from strings to ints
    // A maplet is "k := v," k and v being of types K and V
    var aMap: map<string,int>  := map["Hi" := 1, "There" := 2];

    // Map domain (key) membership
    var isIn: bool := "There" in aMap; // true
    var isntIn := "Their" !in aMap;    // true

    // Finite map cardinality (number of maplets in a map)
    var card := |aMap|;

    //Map lookup
    var image1 := aMap["There"];
    // var image2 := aMap["Their"]; // error! 
    var image2: int;
    if ("Their" in aMap) { image2 := aMap["Their"]; }

    // map update, maplet override and maplet addition
    aMap := aMap["There" := 3];
    aMap := aMap["Their" := 10];  
}


// Dafny supports arrays. Here's we'll see simple 1-d arrays.

method ArrayPlay() 
{
    var a := new int[10]; // in general: a: array<T> := new T[n];
    var a' := new int[10];   // type inference naturally works here
    var i1 := a.Length;      // Immutable "Length" member holds length of array
    a[3] := 3;              // array update
    var i2 := a[3];         // array access
    var seq1 := a[3..8];    // take first 8, drop first 3, return as sequence
    var b := 3 in seq1;     // true! (see sequence operations)
    var seq2 := a[..8];     // take first 8, return rest as sequence
    var seq3 := a[3..];     // drop first 3, return rest as sequence
    var seq4 := a[..];      // return entire array as a sequence
}

