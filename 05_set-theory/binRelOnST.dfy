/*
(c) Kevin Sullivan. 2018.
*/

module binRelST
{    
    /*
    Abstraction of a finite binary relation on 
    sets, S and T. Underlying representation is
    a triple: the domain set, S, the co-domain
    set, T, and a set of pairs over the product
    set, S x T.
    */ 
    class binRelOnST<S(!new,==),T(!new,==)>
    {
        var d: set<S>;      // domain: set of values of type S
        var c: set<T>       // co_domain: set of values of type T
        var p: set<(S,T)>;  // relation: set of pairs from s X t
 
        predicate Valid()
            reads this;
        {
            // tuple elements must be in dom and co_dom, resp.
            forall x, y :: (x, y) in p ==> x in d && y in c
        }


        /*
        Constructor requires that all values appearing in 
        any of the pairs in p be in domain and co_domain sets,
        respectively. A note: the ensures clause really is
        needed here: the bodies of *methods* are not visible
        to the verifier, so if you want the verifier to be
        able to use knowledge of what a method does, you must
        make that behavior explicit in the specification. By
        contrast, in Dafny, function bodies are visible to 
        the verifier, though they can be made "opaque" using
        a special keyword. 
        */
        constructor(domdef: set<S>, codom: set<T>, prs: set<(S,T)>)

            /*
            Ensure that all values in tuples are from dom and co_dom
            sets, respectively. We don't use "Valid" here because we
            haven't constructed the object yet; rather we require that
            the arguments to the construct be valid in the sense that
            when we use them, we will end up with a "Valid" object.
            */
            requires forall x, y :: 
                (x, y) in prs ==> x in domdef && y in codom;

                /*
            Once the constructor finishes, this object should 
            satisfy its state invariant.
            */
            ensures Valid();

        /*
            Explain to verifier what this method accomplishes. The
            verifier needs this information to verify propositions
            elsewhere in this code. It's because method bodies are 
            "opaque" to the verifier, that it can't infer these
            facts from the method body itself. (Function definitions
            are not opaque in this way.)
            */
           ensures  dom_def() == domdef && 
                    co_dom() == codom && 
                    pairs() == prs;

        {
            d := domdef;
            c := codom;
            p := prs;
        }


        /*
        Return domain of definition set. 
        */
        function method dom_def(): (r : set<S>)
            /*
            The Dafny verifier needs to know what 
            values function results depend on. So 
            we have to tell it that the function
            here can read any of the values (the
            data members) in the current function.

            A precondition of this method, and all
            methods, is that the object be in a state
            that is consistent with its invariants;
            and a postcondition is that this method,
            and all methods, also leave it in such
            a state.
            */
            reads this;
            requires Valid();
            ensures r == d;
            ensures Valid();
        {
            d
        }


        /*
        Return co_domain set.
        */
        function method co_dom(): (r : set<T>)
            reads this;
            requires Valid();
            ensures r == c;
            ensures Valid();
        {
            c
        }


        /*
        Return set of ordered pairs
        */
        function method pairs(): set<(S,T)>
            reads this
            requires Valid();
            ensures Valid();
        {
            p
        }

        function method dom() : set<S>
            reads this
            requires Valid();
            ensures Valid();
        {
            set s : S | 
                s in dom_def() &&   // needed to ascertain finiteness
                exists t :: t in co_dom() && (s,t) in pairs() :: s
        }

        function method ran() : set <T>
            reads this
            requires Valid();
            ensures Valid();
        {
            set t : T | 
                t in co_dom() &&
                exists s :: s in dom_def() && (s,t) in pairs() :: t
        }    


        /***********************************/
        /* ARE GIVEN NODES RELATED OR NOT? */
        /***********************************/

        predicate method related(x: S, y: T)
            reads this;
            requires Valid();
            requires x in dom_def() && y in co_dom();
            ensures Valid();
        {
            (x, y) in pairs()
        }


        predicate method unrelated(x: S, y: T)
            reads this;
            requires Valid();
            requires x in dom_def() && y in co_dom();
            ensures Valid();
        {
            (x, y) !in pairs()
        }


        /*******************************/
        /* FUNCTION-RELATED PROPERTIES */
        /*******************************/

        /*
        Return true iff the relation is single-valued (a function)
        */
        predicate method isFunction()
            reads this;
            requires Valid();
            ensures Valid();
        {
            forall x, y, z ::   x in dom_def() && 
                                y in co_dom() && 
                                z in co_dom() &&
                                (x, y) in pairs() && 
                                (x, z) in pairs() ==> 
                                y == z  
        }

        
        /*
        Return true iff the relation is an injective function
        */
        predicate method isInjective()
            reads this;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            forall x, y, z ::   x in dom_def() && 
                                y in dom_def() && 
                                z in co_dom() &&
                                (x, z) in pairs() && 
                                (y, z) in pairs() ==> 
                                x == y  
        }
        
        
        /*
        Return true iff the relation is a surjective function  
        */
        predicate method isSurjective()
            reads this;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            /*
            A function, r, is surjective iff for every y in the co_domain, there is some x in the domain such that the pair (x, y) is in r.
            */ 
            forall y :: y in co_dom() ==> 
                exists x :: x in dom_def() && (x,y) in pairs()
        }


        /*
        Return true iff the relation a bijective function
        */
        predicate method isBijective()
            reads this;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            this.isInjective() && this.isSurjective()    
        }


       /*
        Return true iff the relation is total function
        */
        predicate method isTotal()
            reads this;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            /*
            A function is total if for every x in the 
            domain, there is some y in the co_domain with 
            (x,y) in r
            */
            forall x :: x in dom() ==> 
                exists y :: y in co_dom() && (x,y) in pairs()
        }

        
        /*
        Return true iff the relation is partial (relative to its domain set)

        KEVIN NOTE: There seems to be some inconsistency in the mathematical
        community about whether the partial functions include or exclude the
        total functions.
        */
        predicate method isStrictlyPartialFunction()
            reads this;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            !isTotal()
        }


        /*
        Return true iff this relation is defined 
        for a value that (as a precondition) is in
        the domain of definition of this relation.  
        */
        predicate method isDefinedFor(x: S)
            requires Valid()
            requires x in dom_def();
            reads this;
        {
            exists y :: y in ran() && (x, y) in pairs()
        }


        /*
        Return true iff given value is in range of
        relation: not just in co_domain set but mapped
        to by some value for which relation is defined.
        */
        predicate method inRange(y: T)
            requires Valid()
            requires y in co_dom();
            reads this;
        {
            exists x :: x in dom_def() && (x, y) in pairs()
        }


        /*
        Compute image set of a single value under this relation.
        */
        function method image(x: S): set<T>
            reads this;
            requires Valid(); 
            requires x in dom();
            ensures Valid();
        {
            set y | y in ran() && (x, y) in pairs()
        }


        /*
        Compute preimage set of a value under this relation
        */
        function method preimage(y: T): set<S>
            reads this;
            requires Valid(); 
            requires y in co_dom();
            ensures Valid();
        {
            set x | x in dom() && (x, y) in pairs()
        }


        /*
        Compute image set of a set of values under this relation
        */
        function method imageOfSet(xs: set<S>): set<T>
            reads this;
            requires Valid(); 
            requires forall x :: x in xs ==> x in dom()
            ensures Valid();
        {
            /*
            For each x in the given set of x values (xs) find all
            the (x, y) pairs; return the set of all such y values
            */
            set x, y | x in xs && y in co_dom() && (x, y) in pairs() :: y
        }


        /*
        Compute preimage set of a set of values under this relation.
        */
        function method preimageOfSet(ys: set<T>): set<S>
            reads this;
            requires Valid(); 
            requires forall y :: y in ys ==> y in co_dom();
            ensures Valid();
        {
            set x, y |  y in ys && x in dom_def() && (x, y) in pairs() :: x 
        }


        /*
        Compute image of a domain element under this relation,
        conditional on this relation also being a function.
        This code assumes there is exactly one element in the 
        set from which the value is drawn (but this assumption
        is not yet verified).
        */
        method fimage(x: S) returns (y: T)
            requires Valid(); 
            requires isFunction();  // ensures single-valuedness
            requires x in dom();   // ensures function is non-empty
            requires isDefinedFor(x);
            ensures y in set y' | y' in ran() && (x, y') in pairs();
            ensures 
                exists y, y' :: 
                    (y in ran() && 
                    y' in ran() &&
                    (x, y) in pairs() &&
                    (x, y') in pairs() ==>
                y == y');
            ensures Valid();
        {
            /* 
            Assign to y the one value in the image of x. This
            code depends on the fact that there is exactly one
            element in the image set, because the relation is
            both defined for x and is single-valued (a function).
            However, we haven't verified this assumption.
            */
            y :| y in image(x);
        }


        /*
        Helper function: given a set of pairs, return the set
        of inverted (reversed) pairs.
        */
        static function method invert<S(==),T(==)>(ps: set<(S,T)>) : 
            set<(T,S)>
        {
            set x, y, p | p in ps && x == p.0 && y == p.1 :: (y, x)
        }


        /*
        Construct and return the inverse of this relation.
        */
        method inverse() returns (r: binRelOnST<T,S>)
            requires Valid();
            ensures r.Valid();
            ensures r.dom_def() == co_dom();
            ensures r.co_dom() == dom_def();
            ensures r.pairs() == invert(pairs());
        {
            r := new binRelOnST(co_dom(), dom_def(), invert(pairs()));
        }


        /*
        Helper function: "join" two sets of pairs, g and f,
        returning (g o f), on a common element in the co_domain
        of f and the domain of g. Defining this function once
        here eliminates redundancy in the definition of the 
        compose function, below. 
        
        Along with the two sets of pairs, g and f, this function  takes sets representing the domains and co_domains from which the values in the pairs are drawn: the domain of f, shared co_domain of f and domain of g, and the co_domain of g. 
        */
        static function method comp_helper<X(!new), Y(!new), Z(!new)>
            (g: set<(Y,Z)>, f: set<(X,Y)>, 
             fdom: set<X>, shared: set<Y>, gco_dom: set<Z>): 
            set<(X,Z)>
        {
            set x, z | 
                x in fdom && z in gco_dom &&
                exists y :: y in shared && 
                (x, y) in f && (y, z) in g :: (x,z)
            /*
            set x, y, z | 
                x in fdom && y in shared && z in gco_dom &&
                (x, y) in f && (y, z) in g :: (x, z)

                               comp_helper(    
                                g.pairs(),
                                this.pairs(), 
                                this.dom(), 
                                g.dom_def(),
                                g.co_dom())

            */
        }


        /*
        Returns h, the composition of "this" relation, from S to T, 
        with the relation, g, from T to R, yielding the relation, r,
        from S to R. S-values to R-values. 
        */
        method compose<R>(g: binRelOnST<T,R>) 
            returns (h : binRelOnST<S,R>)
            requires this.Valid();
            requires g.Valid();
            requires g.dom_def() == this.co_dom();
            ensures h.Valid();
            ensures h.dom_def() == this.dom_def();
            ensures h.co_dom() == g.co_dom();
            ensures h.pairs() == 
                comp_helper(    g.pairs(),
                                this.pairs(), 
                                this.dom(), 
                                g.dom_def(),
                                g.co_dom())
            ensures forall x, z :: 
                (x, z) in h.pairs() ==> x in dom() && z in g.co_dom();
        {
            h := new binRelOnST<S, R>
                (
                    this.dom_def(),  
                    g.co_dom(), 
                    comp_helper(g.pairs(), pairs(), dom(), g.dom_def(), g.co_dom())
                );
        }
    }
}