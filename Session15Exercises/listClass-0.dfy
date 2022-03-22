class Node {
    var val: int;
    var next: Node?    
    ghost var repr: set<object>;
    ghost var model : seq<int>;

    predicate Valid() 
    reads this, repr
//  decreases repr
    {
        (next == null ==> model == [val]) &&
        this in repr && 
        (next != null ==> 
                next in repr && next.repr <= repr && this !in next.repr && next.Valid()
                && model == [val] + next.model
        )
    }

    constructor (v: int) 
    ensures Valid()
    ensures fresh(repr)
    ensures model == [v]
    ensures repr == {this}
    ensures this in repr
    {
        val  := v;
        next := null;
        repr := {this};
        model := [v];
        
    }

    function length() : nat
    //reads this
    reads repr
    requires Valid()
    ensures length () == |model|
    {
        if next == null then 1 else 1 + next.length()
    }
    
    method append (node: Node)
    requires forall k::k in repr ==> k !in node.repr
    requires Valid()
    requires node.Valid()
    modifies repr
    //modifies this
    ensures Valid()
    ensures model == old(model) + node.model
    ensures repr == old(repr) + node.repr;
    decreases repr
    {
        if next == null {
            next := node;
        }
        else{
            
            next.append(node);
        }
        model := [val] + next.model;
        repr := repr + next.repr;
    }
}

class List {
    var first : Node?;
    ghost var repr: set<object>;
    ghost var model: seq<int>;

    
    predicate Valid() 
    reads this, repr
    {
        (first == null ==> model == []) && 
        this in repr && 
        (first != null ==> first in repr && 
        (model == first.model) && 
        first.repr <= repr && 
        this !in first.repr && 
        first.Valid())
    }

    constructor () 
    ensures Valid()
    ensures fresh(repr)
    ensures model == []
    {
        first := null;
        repr := {this};
        model := [];
    }    

    function length (): nat
    reads this
    reads repr
    requires Valid()
    ensures length () == |model|
    {
        if first == null then 0 else first.length()
    }

    // This adds an element to the left of the list
    method add (v: int)
    modifies this
    modifies repr
    requires Valid()
    ensures Valid()
    ensures model == [v] + old(model)
    ensures fresh(repr - old(repr))
    {
        var node := new Node(v); 
        if first == null {
            node.repr := {node};
            node.model := [v];
        }
        else {
            node.repr := {node} + first.repr;
            node.model := [v] + first.model;
        }
        first, node.next := node, first;
        repr := repr + {node};
        model := first.model;
    }

    // This method adds an element to the end of the list
    method append(v: int)
    requires Valid()
    //modifies this
    modifies repr
    ensures model == old(model) + [v]
    ensures Valid()
    ensures fresh(repr - old(repr))
    {
        var node := new Node(v);
        if first == null {
            first := node;
        }
        else{
            first.append(node);
        }
        repr := repr + {node};

        model := model + [v];
    }
    
 }

method Main ()
{
    var l := new List();
    assert l.length () == 0;
    l.add(1);
    assert l.length () == 1;
    l.add(2);
    assert l.length() == 2;
    l.append(7);
    //assert l.model() == [2,1,7];
}

/*
   Exercise: 
   
   implement and verify append methods in classes Node and List,
   which adds a new element to the right of the list.

    requires Valid()
    ensures Valid()
    ensures model == old(model)+ [v]
    modifies repr 
 
*/  
