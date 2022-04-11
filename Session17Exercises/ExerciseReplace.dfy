//Author: Clara Segura
include "List.dfy"


method replace(l:List,x:int,y:int)
modifies l,l.Repr()
requires l.Valid()
requires forall x | x in l.Repr() :: allocated(x)

ensures l.Valid() //inv

//ensures: write the properties concerning the model
//replace each occurrence of x by y, and leave the rest unchanged 
ensures |l.Model()| == |old(l.Model())|
ensures forall i| 0<=i<|old(l.Model())| && old(l.Model())[i]==x :: l.Model()[i]==y
ensures forall i| 0<=i<|old(l.Model())| && old(l.Model())[i]!=x :: l.Model()[i]==old(l.Model())[i]

ensures l.Iterators() >= old(l.Iterators())

//copy this to invariant
ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
ensures fresh(l.Repr()-old(l.Repr()))
ensures forall x | x in l.Repr() :: allocated(x)
{
    var it:=l.Begin();
    while(it.HasNext())
    invariant l.Valid()
    invariant it.Valid()
    invariant it.Parent() == l
    invariant l.Size() == old(l.Size())
    decreases l.Size() - it.Index()
    invariant it.Index() <= l.Size()
    invariant l.Iterators() >= old(l.Iterators())
    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant forall x | x in l.Repr() :: allocated(x)
    invariant forall i| it.Index()<=i<l.Size() :: l.Model()[i]==old(l.Model())[i]
    invariant forall i| 0<=i<it.Index() && old(l.Model())[i]==x :: l.Model()[i]==y
    invariant forall i| 0<=i<it.Index() && old(l.Model())[i]!=x :: l.Model()[i]==old(l.Model())[i]
    {

        if(it.Peek() == x){
            it.Set(y);
        }
        var xx:=it.Next();
    }
    
}



