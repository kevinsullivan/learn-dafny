/*
(c) Kevin Sullivan. 2018.
*/

/*
This class provides an abstraction of a polymorphic
finite binary relation over a single set, S, of 
elements of an equality-supporting type, S. There
is no class inheritance in Dafny, so we can't just
inherit from and extend BinRelST. Rather we wrap
and delegate to a private instance of BinRelST.
*/

include "binRelOnST.dfy"

module binRelS
{    
    import opened binRelST
    /*    
    The concrete representatation of a value of
    this type is just an object of the binRelOnST
    class, where both of its type parameters are
    T, and where the domain and codomain sets are
    just S. This class specializes (restricts) 
    the more general binRelOnST class. Some of 
    the basic operations of this class "delegate"
    to the underlying relation object, which is 
    to say, operations of this class work simply
    by calling corresponding operations on the
    underlying concrete representation object. 
    */ 
    class binRelOnS<S(!new,==)>
    {
        /*****************************/
        /* STATE AND STATE INVARIANT */
        /*****************************/


        /*
        STATE: Concrete representation: a binary 
        relation on S X T where both sets are of
        the same type, T.
        */
        var r: binRelOnST<S,S>;


        /*
        INVARIANT: This object is valid if it's a 
        valid relation on S X T and the domain and 
        codomain are the same set: not just sets of
        the same type, but exactly the same set.
        */
        predicate Valid()
            reads this;
            reads r;
        {
            r.Valid() && r.dom_def() == r.co_dom()
        }


        /*****************************/
        /* CONSTRUCTOR AND ACCESSORS */
        /*****************************/

        /*
        This constructor instantiates a binary relation
        on S X T using type, T, for both type parameters,
        a single set for the both the domain and codomain
        sets, and a set of T-T pairs as the relation, with
        the constraint that values in the relation be from
        the domain/codomain set.
        */
        constructor(aSet: set<S>, prs: set<(S,S)>)
            /*
            The relation has to be over the given set.
            */
            requires forall x, y :: 
                (x, y) in prs ==> x in aSet && y in aSet;
            
            /*
            Note that the following ensures must come
            before the subsequent "ensures" clause, as
            that clause calls functions that require
            Valid() to be true.
            */
            ensures Valid();

            /*
            Dafny can't see into *method* bodies (they
            are thus said to be "opaque"), so we have to
            express what this method achieves as part of 
            its specification, to enable verification of
            subsequent propositions about this class.
            */
            ensures dom_def() == aSet && 
                    co_dom() == aSet && 
                    pairs() == prs;
            
            {
                r := new binRelOnST(aSet,aSet,prs);
            }


        /*
        Accessor (projection) function: return the domain 
        set. The codom() and getSet() methods return the 
        same result. The three are provided for the sake
        of the completeness of the abstraction we define
        here.
        */
        function method dom(): set<S>

            /*
            Every operation (function, method) of this 
            class except for the constructor require that
            an object be in a valid state for the operation
            to be applied. Every method is also required to
            ensure that it leaves this object in a valid
            state, so ensures Valid() is also included 
            below and in every other method. The idea is
            that the constructor establises the property
            of being valid, and every method preserves it,
            so it is an *invariant* property of objecst of
            this type. Specifying and ensuring preservation
            of state invariants of objects is essential,
            and the failure to do so properly is a major
            source of bugs in code.
            */
            requires Valid();
 
            /*
            Dafny needs to know what values a function reads
            in order to know what values its results might
            depend on, for purposes of later verifications.
            The "reads this" specification element informs
            the verifier that this function might read any 
            of the fields of this object.
            */
            reads this;

            /*
            This specification element, "reads r" tells Dafny
            that his function can call functions that in turn
            read fields of r.
            */
            reads r;

            /*
            As explained above, this (and every) operation is
            requires to leave this object in a valid state.
            */
            ensures Valid();
        {
            /*
            After all that, we just "delegate" this operation
            to the corresponding operation of the underlying
            binRelOnST object, by calling r.dom(). That this
            operation leaves the object in a valid state thus
            relies on r.dom() doing so. And that is the case,
            because Dafny verifies that function as doing so.
            */
            r.dom()
        }


        function method dom_def(): set<S>
            requires Valid();
            reads this;
            reads r;
            ensures Valid();
        {
            r.dom_def()
        }


        function method co_dom(): set<S>
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            r.co_dom()
        }
        
        
        function method ran(): set<S>
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            r.ran()
        }


        /*
        Accessor/projection function: return the 
        relation (pair set).
        */
        function method pairs(): set<(S,S)>
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            r.pairs()
        }

        /***********************************/
        /* ARE GIVEN NODES RELATED OR NOT? */
        /***********************************/

        predicate method related(x: S, y: S)
            reads this;
            reads r;
            requires Valid();
            requires x in dom_def() && y in co_dom();
            ensures Valid();
        {
            r.related(x, y)
        }

        /*********************************/
        /* BASIC PROPERTIES OF FUNCTIONS */
        /*********************************/

        predicate method isFunction()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            r.isFunction()  
        }


        /*** 
        PROPERTIES OF FUNCTIONS, IN PARTICULAR.        
        The properties of being injective, surjective, 
        or bijective apply to single-valued relations,
        i.e., to functions. The next three properties 
        only apply to relations that are also functions: 
        that satisfy the isFunction() predicate. We thus
        add "isFunction()"" as a pre-condition to each
        of these operations. We then implement them by
        simply calling the corresponding operations on
        the concrete representation object, r, which
        returns the answer we require.
        ***/


        /*
        Return true iff this relation is an injection.
        */
        predicate method isInjective()
            reads this;
            reads r;
            requires Valid();
            requires isFunction();  // newprecondition
            ensures Valid();
        {
            r.isInjective()
        }
        
        
        /*
        Return true iff the relation is a function and 
        it is a surjective function, in particular. 
        */
        predicate method isSurjective()
            reads this;
            reads r;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            r.isSurjective()
        }


        /*
        Return true iff the relation is a function 
        and is bijective, in particular. 
        */

        predicate method isBijective()
            reads this;
            reads r;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            r.isBijective()    
        }


       /*
        Return true iff the relation is total 
        (i.e., defined on every element of its
        domain set).
        */
        predicate method isTotalFunction()
            reads this;
            reads r;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            r.isTotal()
        }

        
        /*
        Return true iff the relation is partial 
        (not total relative to its domain set).
        */
        predicate method isStrictlyPartialFunction()
            reads this;
            reads r;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            !r.isTotal()
        }


                /****************************************************/
        /* BASIC PROPERTIES OF ENDORELATIONS MORE GENERALLY */
        /****************************************************/

        /*
        Return true iff this relation is reflexive.
        To be reflexive a relation must map every
        element of its domain to itself. 

        This function provides a good simple example
        of a unversally quantified predicate in Dafny.
        It can be read as "forall x (implicitly of type
        T), if x is in the domain of this relation then
        (x,x) is in the relation." The following few
        functions are written in the same style. What
        you have in these cases, then, is simply the
        mathematical definitions of these fundamental
        properties of relations expressed using Dafny 
        syntax.
        */
        predicate method isReflexive()
            reads this;
            reads r;
            requires Valid();
            ensures Valid(); 
        {
            forall x :: x in dom_def() ==> related(x, x)
        }

                /*
        A relation on a set S is said to be irreflexive
        if no element is related to, or maps, to itself.
        As an example, the less than relation on natural
        numbers is irreflexive: not natural number is less
        than itself.
        */
        predicate method isIrreflexive()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            forall x :: x in dom_def() ==> !related(x,x)
        }


        /*
        A binary relation on a set, S, is said to be 
        quasi-reflexive if every element that is related
        to some other element is also related to itself.

        Adapted from Wikipedia: An example is a relation 
        "has the same limit as" on infinite sequences of 
        real numbers. Recall that some such sequences do
        converge on a limit. For example, the infinite
        sequence, 1/n, for n = 1 to infinity, converges
        on (has limit) zero. Not every sequence of real
        numbers has such a limit, so the "has same limit
        as" relation is not reflexive. But if on sequence 
        has the same limit as some other sequence, then 
        it has the same limit as itself.
        */
        predicate method isQuasiReflexive()
             reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            forall x, y :: 
                x in dom_def() && 
                y in co_dom() && 
                related(x, y) ==> 
                related(x, x)
        }



        /*
        Return true iff the relation is symmetric
        */
        predicate method isSymmetric()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            forall x, y ::  x in dom_def() && y in dom_def() &&
                            related(x, y) ==> related (y, x)
        }

        
        /*
        A binary relation is said to be antisymmetric
        if whenever both (x, y) and (y, x) are in the
        relation, it must be that x == y. A canonical
        example of an antisymmetric relation is <= on
        the natural numbers. If x <= y and y <= x (and
        that is possible) then it must be that x == y.
        */
        predicate method isAntisymmetric()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            forall x, y ::  x in dom_def() &&
                            y in dom_def() &&
                            related (x, y)&&
                            related (y,x) ==> 
                            x == y
            // Note: equivalent to xRy ==> !yRx
        }

        /*
        A binary relation, R, is said to be asymmetric 
        (as distinct from anti-symmetric) if it is both
        anti-symmetric and also irreflexive. The latter
        property rules out an element being related to
        itself. Think of it as removing the possibility
        of being "equal" in an otherwise anti-symmetric
        (such as less than or equal) relation.
        
        More precisely, in an asymmetric relation, for 
        all elements a and and b, if a is related to b 
        in R, then b is not and cannot be related to a. 
        
        The canonical example of an asymmetric relation
        is less than on the integers. If a < b then it 
        cannot also be that b < a. To be asymmetric is 
        the same as being antisymmetric and irreflexive.
        */
        predicate method isAsymmetric()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            isAntisymmetric() && isIrreflexive()
        }


        /*
        Return true iff the relation is transitive
        */
        predicate method isTransitive()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            forall x, y, z ::  
                x in dom_def() && y in dom_def() && z in dom_def() &&
                related (x, y) && 
                related (y, z)  ==> 
                related (x, z) 
        }


        /*
        Exercise: formalize and implement a test for being
        an equivalence relation.
        */
       predicate method isEquivalence()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            isReflexive() && isSymmetric() && isTransitive()
            //Note: equivalent to isPreorder() && isSymmetric() 
        }


        /*************************************/
        /**** BASIC ORDER THEORY CONCEPTS ****/
        /*************************************/

        /*
        A relation is said to be a "preorder" if it is
        reflexive and transitive. That is, every element
        is related to itself, and if e1 is related to e2
        and e2 to e3, then e1 is also related to e3. 
        
        A canonical example of a preorder is the
        *reachability relation* for a directed graph: 
        every element reaches itself and if there's 
        a *path* from a to b then a is said to reach b. 

        Subtyping relations are also often preorders.
        Every type is a subtype of itself, and if A is
        a subtype of B, B of C, C ..., of E, then A is
        also a subtype of B, C, ..., E.

        Given any relation you can obtain a preorder
        by taking its reflexive and transitive closure.
 
        Unlike a partial order, a preorder in general 
        is not antisymmetric. And unlike an equivalence
        relation, a preorder is not necesarily symmetric.
        */
        predicate method isPreorder()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            isReflexive() && isTransitive() 
        }

        /*
        A binary relation is a partial order if it is
        a preorder (reflexive and transitive) and also
        anti-symmetric. Recall that anti-symmetry says
        that the only way that both (x, y) and (y, x) 
        can be in the relation at once is if x==y.
        
        A canonical example of a partial order is the 
        "subset-of" relation on the powerset of a given
        set. It's reflexive as every set is a subset of 
        itself. It's anti-symmetric because if S is a
        subset of T and T is a subset of S then T=S.
        And it's transitive, because if S is a subset 
        of T and T a subset of R then S must also be 
        a subset of R. 
        
        This relation is a *partial* order in that not 
        every pair of subsets of a set are "comparable," 
        which is to say  it is possible that neither 
        is a subset of the other. The sets, {1, 2} and 
        {2, 3}, are both subsets of the set, {1, 2, 3},
        for example, but neither is a subset of the
        other, so they are not "comparable:" There is 
        no pair of these two sets, in either order, in
        the "subset-of" relation.

        A partial order in order theory corresponds 
        directly to a "directed acyclic graph" (DAG)
        in graph theory.
        */
        predicate method isPartialOrder()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            isPreorder() && isAntisymmetric()
        }


        /*
        We now define what it means for a binary relation 
        to be "total," also called "complete." NOTE WELL!
        The term, "total", means something different when
        applied to binary relations, in general, than to 
        functions, in particular. A function is total if 
        for every x in S there is *SOME* y to which it is 
        related (or mapped, as we say). We thus provide 
        isTotalFunction and isPartialFunction predicates 
        (with Function in the names) to capture this idea.
        
        By contrast, a binary relation (more generally) 
        is said to be total, or "complete", if for *any* 
        pair of values, x and y in S, either (or both) 
        of (x, y) or (y, x) is in the relation.

        A simple example of a total relation is the less
        than or equals relation on integers. Given any 
        two integers, x and y, it is always the case that
        either x <= y or y <= x, or both if they're equal.

        Anoather example of a total binary relation
        is what economists call a preference relation. A
        preference relation is a mathematical model of 
        a consumer's preferences. It represents the idea
        that given *any* two items, or outcomes, x and y,
        one will always find one of them to be "at least 
        as good as" the other. These ideas belong to the 
        branch of economics called "utility theory." 

        The broader point of this brief diversion into 
        the field of economics is to make it clear that
        what seem like very abstract concepts (here the
        property of a binary relation being complete or
        not) have deep importance in the real world: in
        CS as well as in many other fields.

        We can now formalize the property of being total.
        A binary relation, R, on a set, S, is said to be 
        "complete," "total" or to have the "comparability" 
        property if *any* two elements, x and y in S, are 
        related one way or the other by R, i.e., at least 
        one of (x, y) and (y, x) is in R.
        */
        predicate method isTotal()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            forall x, y :: x in dom_def() && y in co_dom() ==> 
                 related(x, y) || related(y, x)
        }

        
        // isComplete() is a synonym for isTotal()
        predicate method isComplete()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            isTotal()
        }



        /*
        The kind of order most familiar from elementary
        mathematics is a "total" order. The natural and
        real numbers are totally ordered under the less
        than or equals relation, for example. Any pair 
        of such numbers is "comparable." That is, given
        any two numbers, x and y, either (x, y) or (y, x)
        is (or both are) in the "less than or equal 
        relation." 

        A total order, also known as a linear order, a 
        simple order, or a chain, is a partial order with
        the additional property that any two elements, x
        and y, are comparable. This pair of properties
        arranges the set into a fully ordered collection. 

        A good example is the integers under the less than
        or equal operator. By contrast, subset inclusion is
        a partial order, as two sets, X and Y, can both be
        subsets of ("less than or equal to") a set Z, with
        neither being a subset of the other.
        */
        predicate method isTotalOrder()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            isPartialOrder() && isComplete()
        }


        /*
        A binary relation is said to be coreflexive if 
        for all x and y in S it holds that if xRy then 
        x = y. A coreflexive relation is a subset of an
        identity relation, in which *every* element is 
        related to, and only to, itself. A relation is 
        thus co-reflexive if it relates some object to,
        and only to, themselves.
        
        For example, if every odd number is related itself
        under an admittedly "odd" version of equality, then
        this relation is coreflexive.
        */
        predicate method isCoreflexive()
            reads this;
            reads r;
            requires Valid();
            ensures Valid(); 
        {
            forall  x, y :: x in dom_def() && 
                    y in co_dom() && 
                    related (x,y) ==> 
                    x == y
        }

        /*********************************************/
        /**** MORE ADVANCED ORDER THEORY CONCEPTS ****/
        /*********************************************/

        /*
        A total preorder is preorder in which every
        pair of elements is comparable, e.g., for every 
        node a and b, either a reaches b or b reaches a. 
        That is, there are no pairs of elements that are 
        *incomparable*. 

        BETTER EXAMPLE NEEDED

        */
        predicate method isTotalPreorder()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
            {
                isPreorder() && isTotal()
            }


       /*
        A relation R is a strict partial order if it's
        irreflexive, antisymmetric, and transitive. A
        canonical example is the less than (<) relation
        on a set of natural numbers. 
        */
        predicate method isStrictPartialOrder()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            isIrreflexive() && isAntisymmetric() && isTransitive()
        }

        /*
        A relation R is said to be a quasi-order if it
        is irreflexive and transitive. 
        
        The less than and proper subset inclusion 
        relations are quasi-orders but not partial 
        orders, because partial orders are necessarily 
        also reflexive. The less than or equal and 
        subset inclusion relations are partial orders 
        but not quasi-orders because they are reflexive.

        Compare with strict partial ordering, which is 
        a quasi-order that is also anti-symmetric.

        This definition of quasi order is from Stanat and 
        McAllister, Discrete Mathematics in Computer Science, 
        Prentice-Hall, 1977. Others define quasi-order as 
        synonymous with preorder. See Rosen, Discrete 
        Mathematicas and Its Applications, 4th ed., 
        McGraw-Hill, 1999.
        */
        predicate method isQuasiOrder()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            isIrreflexive() && isTransitive() 
        }


        /*
        Weak ordering

        "There are several common ways of formalizing weak
        orderings, different from each other but cryptomorphic 
        (interconvertable with no loss of information): they may be 
        axiomatized as strict weak orderings (partially ordered sets 
        in which incomparability is a transitive relation), as total 
        preorders (transitive binary relations in which at least one 
        of the two possible relations exists between every pair of 
        elements), or as ordered partitions (partitions of the 
        elements into disjoint subsets, together with a total order 
        on the subsets)....
        
        ... weak orders have applications in utility theory. In 
        linear programming and other types of combinatorial 
        optimization problem, the prioritization of solutions or 
        of bases is often given by a weak order, determined by a 
        real-valued objective function; the phenomenon of ties 
        in these orderings is called "degeneracy", and several 
        types of tie-breaking rule have been used to refine this 
        weak ordering into a total ordering in order to prevent 
        problems caused by degeneracy.

        Weak orders have also been used in computer science, in 
        partition refinement based algorithms for lexicographic 
        breadth-first search and lexicographic topological ordering. 
        In these algorithms, a weak ordering on the vertices of 
        a graph (represented as a family of sets that partition 
        the vertices, together with a doubly linked list providing 
        a total order on the sets) is gradually refined over the 
        course of the algorithm, eventually producing a total 
        ordering that is the output of the algorithm.

        In the Standard (Template) Library for the C++ programming 
        language, the set and multiset data types sort their input 
        by a comparison function that is specified at the time of 
        template instantiation, and that is assumed to implement 
        a strict weak ordering." --Wikipedia 

        We formalize the concept as "total preorder." 
        */
        predicate method isWeakOrdering()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            isTotalPreorder()
        }

 
        /*
        A strict weak ordering is a strict partial order 
        in which the relation "neither a R b nor b R a" is
        transitive. That is, for all x, y, z in S, if neither
        x R y nor y R x holds, and if neither y R z nor z R y
        holds, then neither x R z nor z R x holds.

        In the C++ Standard Template Library (STL), if you want to use
        a standard sort routine or map data structure you have to define 
        an overloaded < operator; and it has to imlpement a strict weak
        ordering relation.

        From StackOverflow:

        This notion, which sounds somewhat like an oxymoron, 
        is not very commonly used in mathematics, but it is in 
        programming. The "strict" just means it is the irreflexive 
        form "<" of the comparison rather than the reflexive "≤". 
        The "weak" means that the absence of both a<b and b<a do 
        not imply that a=b. However as explained here, the relation 
        that neither a<b nor b<a holds must be an equivalence relation. 
        The strict weak ordering then induces a (strict) total 
        ordering on the equivalence classes for this equivalence 
        relation.

        This notion is typically used for relations that are in 
        basically total orderings, but defined using only partial 
        information about the identity of items. For instance 
        if a<b between persons means that a has a name that 
        (strictly) precedes the name of b alphabetically, then
        this defines a strict weak order, since different persons
        may have identical names; the relation of having 
        identical names is an equivalence relation.

        One can easily show that for a strict weak ordering "<", 
        the relation a≮b is (reflexive and) transitive, so it 
        is a pre-order,and the associated equivalence relation 
        is the same as the one associated above to the strict 
        weak ordering. In fact "a≮b" is a total pre-order which 
        induces the same total ordering (or maybe it is better 
        to say the opposite ordering, in view of the negation)
        on its equivalence classes as the strict weak ordering
        does. I think I just explained that the notions of 
        strict weak ordering and total pre-order are equivalent. 
        The WP article also does a reasonable job explaining this.

        Marc van Leeuwen:
        If you are comparing strings, then you would often just 
        define a total ordering (which is a special case of a 
        strict weak ordering) like lexicographic ordering. 
        However, it could be that you want to ignore upper 
        case/lower case distinctions, which would make it 
        into a true weak ordering (strings differing only 
        by case distinctions would then form an equivalence 
        class).

        Note: isStrictWeakOrdering <==> isTotalPreorder (should verify)
        */
        predicate method isStrictWeakOrdering()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            isStrictPartialOrder() && 
            // and transitivity of incomparability
            // i.e., transitivity of unrelatedness
            forall x, y, z :: 
                x in dom_def() && 
                y in dom_def() && 
                z in dom_def() &&
               !related(x, y) && 
               !related(y, z) ==> 
               !related(x, z)
        }


        /*
        A relation R on a set, S, is said to be well-founded
        if every non-empty subset, X, of S has a "minimum"
        element, such that there is no other element, x, in
        X, such that (x, min) is in X.

        As an example, the the less than relation over the
        infinite set of natural numbers is well founded 
        because in any subset of the natural numbers there 
        is always a minimal element, m, an element that is
        less than every other element in the set. On the
        other hand, the less than relation on the integers
        is not well founded. For example in the set of all
        integers less than zero there is no least element.
        
        The concept of being well founded is essential for
        reasoning about when recursive definitions are valid.
        In a nutshell, each recursive call has to be moving
        "down" a finite chain to a minimum element, at which
        point a non-recursive base case must apply. Another
        way to explain being well-founded is that a relation
        is not well founded if there's a way either to "go 
        down forever" or to "go around in circles" forever.
        
        Here we give a version of well foundedness only for 
        finite relations (there can never be an infinite 
        descending chain); what this predicate basically 
        rules out, therefore, are cycles in a relation.
        */
        predicate method isWellFounded()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            forall X | X <= dom_def() ::
                X != {} ==>
                exists min :: min in X && 
                forall s :: s in X ==> 
                !related(s, min)
        }

        /*************** END OF ORDER THEORY****************/




        /*
        A binary relation is said to be a dependency relation 
        if it is finite, symmetric, and reflexive. That is, 
        every element "depends on" itself, and if one depends
        on another, then the other depends on the first. The
        name, "mutual dependency" or "symmetric dependency"
        relation would make sense here.
        */
        predicate method isDependencyRelation()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            isSymmetric() && isReflexive()
        }


        /*
        A binary relation is said to be trichotomous if
        for any pair of values, x and y, xRy or yRx or 
        x==y. The < relation on natural numbers is
        an example of a trichotomous relation: given any
        two natural numbers, x and y, either x < y or
        y < x, or, if neither condition holds, then it
        must be that x = y.
        */
        predicate method isTrichotomous()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            forall x, y :: x in dom_def() && y in dom_def() ==>
                (related(x, y) && !related(y,x) && x!=y) || 
                (related (y, x) && !related(x,y) && x != y) || 
                (!related(x,y) && !related(y,x) && x == y)
        }


        /*
        Right Euclidean: for all x, y and z in X it holds that if xRy and xRz, then yRz.
        */
        predicate method isRightEuclidean()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            forall x, y, z :: x in dom_def() && y in dom_def() && z in dom_def() ==>
                related (x, y) && related (x, z) ==> related(y, z)
        }

        /*
        Left Euclidean: for all x, y and z in X it holds that if yRx and zRx, then yRz.
        */
        predicate method isLeftEuclidean()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            forall x, y, z :: x in dom_def() && y in dom_def() && z in dom_def() ==>
                related(y, x) && related(z, x) ==> related (y, z)
        }

        /*
        Euclidean: A relation is said to be Euclidean if it 
        is both left and right Euclidean. Equality is a Euclidean 
        relation because if x=y and x=z, then y=z.
        */
        predicate method isEuclidean()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            isLeftEuclidean() && isRightEuclidean()
        }

        /*********************************************
         **** Methods for computing new relations ****
         ********************************************/

                 /*
        Return the union of this relation and the given 
        relation, t: b, basicaly (this + t), viewed as sets
        of pairs. The domain/codomain sets of this and t 
        must be the same.
        */
        method relUnion(t: binRelOnS<S>) returns (r: binRelOnS<S>)
            requires Valid();
            requires t.Valid();
            requires t.dom_def() == dom_def();
            ensures r.Valid();
            ensures r.dom_def() == dom_def();
            ensures r.pairs() == t.pairs() + pairs();
        {
            r := new binRelOnS(dom_def(), t.pairs() + pairs());
        }


        /*
        Return the intersection between this relation and 
        the given relation, t: b, basicaly (this * t). The
        domain/codomain sets of this and t must be the same.
        */
        method relIntersection(t: binRelOnS<S>) 
            returns (r: binRelOnS<S>)
            requires Valid();
            requires t.Valid();
            requires t.dom_def() == dom_def();
            ensures r.Valid();
            ensures r.dom_def() == dom_def();
            ensures r.pairs() == t.pairs() * pairs();
        {
            r := new binRelOnS(dom_def(),t.pairs() * pairs());
        }


        /*
        Return the difference between this relation and 
        the given relation, t: b, basicaly (this - t). The
        domain/codomain sets of this and t must be the same.
        */
        method relDifference(t: binRelOnS<S>) 
            returns (r: binRelOnS<S>)
            requires Valid();
            requires t.Valid();
            requires t.dom_def() == dom_def();
            ensures r.Valid();
            ensures r.dom_def() == dom_def();
            ensures r.pairs() == pairs() - t.pairs();
        {
            r := new binRelOnS(dom_def(), pairs() - t.pairs());
        }
      
        


        /*
        The inverse of this relation is a relation on the 
        same set with all the same tuples but in reverse 
        order.
        */
        method inverse() returns (r: binRelOnS<S>)
            requires Valid();
            ensures r.Valid();
            ensures r.dom_def() == co_dom();
            ensures r.co_dom() == dom_def();
            ensures r.pairs() == set x, y | 
                x in dom_def() && y in co_dom() && related(x, y) :: (y, x);
            ensures Valid();
        {
            var invPairs := set x, y | 
                x in dom_def() && y in co_dom() && related(x, y) :: (y, x);
             r := new binRelOnS(dom_def(), invPairs);
        }
        
        
        /*
        Returns the identity relation on the domain
        of this relation. Used, among other things, to
        compute reflexive closures.
        */
        method identity() returns (id: binRelOnS<S>)
            requires Valid();
            ensures id.Valid();
            ensures id.dom_def() == dom_def();
            ensures id.pairs() == set x | x in dom_def() :: (x,x);
            ensures Valid();
        {
             id := new binRelOnS(dom_def(), set x | x in dom_def() :: (x,x));
        }


         /*
        Return the relation g composed with this 
        relation, (g o this). The domain/co-domain
        of g and this must be the same.
        */
        method compose(g: binRelOnS<S>) returns (c : binRelOnS<S>)
            requires Valid();
            requires g.Valid();
            requires g.dom_def() == co_dom();
            ensures c.Valid();
            ensures c.dom_def() == dom_def();
            ensures c.co_dom() == g.co_dom();
            ensures c.pairs() == set r, s, t | 
                    r in dom_def() &&
                    s in co_dom() &&
                    related(r, s) &&
                    s in g.dom_def() && 
                    t in g.co_dom() &&
                    g.related(s, t) ::
                    (r, t);
        {
            var prs := set r, s, t | 
                    r in dom_def() &&
                    s in co_dom() &&
                    related(r, s) &&
                    s in g.dom_def() && 
                    t in g.co_dom() &&
                    g.related(s, t) ::
                    (r, t);
            c := new binRelOnS(dom_def(), prs);
            assert co_dom() == old(co_dom());       // why needed?     
        }

        /*
        The reflexive closure is the smallest relation
        that contains this relation and is reflexive. In
        particular, it's the union of this relation and
        the identity relation on the same set. That is
        how we compute it here.
        */
        method reflexiveClosure() returns (r: binRelOnS<S>)
            requires Valid();
            ensures r.Valid();
            ensures r.dom_def() == dom_def();
            ensures r.pairs() == this.pairs() + 
                                 set x | x in dom_def() :: (x,x);
            //ensures pairs() <= r.pairs();
            ensures Valid();
        {
            var id := this.identity();
            r := relUnion(id);
        }
 

        /*
        The symmetric closure is the smallest relation
        that contains this relation and is symmetric. In
        particular, it's the union of this relation and
        the inverse relation on the same set. It can be
        derived from this relation by taking all pairs,
        (s, t), and making sure that all reversed pairs, 
        (t, s), are also included.
        */
        method symmetricClosure() returns (r: binRelOnS<S>)
            requires Valid();
            ensures r.Valid();
            //ensures r.dom_def() == dom_def();
            ensures r.pairs() == pairs() + set x, y | 
                x in dom_def() && y in co_dom() && related(y, x) :: (x, y);
            //ensures pairs() <= r.pairs();
            ensures Valid();
        {
            var inv := this.inverse();
            r := relUnion(inv);
        }
         
    }
}