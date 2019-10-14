/*
Equality.
*/

predicate set_eq<A(!new)>(S: set<A>, T: set<A>)
{
    forall x :: x in S <==> x in T
}

/*
Subset.
*/
predicate set_subseteq<A(!new)>(S: set<A>, T: set<A>)
{
    forall s :: s in S ==> s in T
}

/*
Proper Subset.
*/
predicate set_subset<A(!new)>(S: set<A>, T: set<A>)
{
    forall s :: s in S ==> s in T && (exists t :: t in T && t !in S)
}

function intersection<A>(S: set<A>, T: set<A>): set<A>
{
    set e | e in S && e in T
}

function union<A>(S: set<A>, T: set<A>): set<A>
{
    //set e | e in S || e in T
    {}
    // Dafny's implementation is incomplete.
    // It can't infer resulting set is finite
    // even though both S and T clearly are.
    // This is a missing-feature bug in Dafny.
}

function set_minus<A>(T: set<A>, S: set<A>): set<A>
{
    set e | e in T && e !in S
}

function method set_product<A,B>(S: set<A>, T: set<B>): set<(A,B)>
{
    set s, t | s in S && t in T :: (s,t)
}

function method power_set<A>(S: set<A>) : set<set<A>>
{
    set s | s <= S
}