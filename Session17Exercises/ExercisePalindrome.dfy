//Author: Clara Segura
include "Stack.dfy"
include "Queue.dfy"
include "List.dfy"
include "Utils.dfy"


lemma compseqs<A>(s1:seq<A>,s2:seq<A>,x:A,y:A)
requires [x]+s1==[y]+s2 && |s1|==|s2|
ensures x==y && s1==s2
{ assert x!=y ==> ([x]+s1)[0] == x != y == ([y]+s2)[0];
  assert forall i::0<=i<=|s1| ==> ([x]+s1)[i]==([y]+s2)[i];
  assert  forall i::0<=i<|s1| ==> s1[i]==([x]+s1)[i+1]==([y]+s2)[i+1]==s2[i];
  
}


method fillStack(l:List,s:Stack)
modifies l,l.Repr(), s, s.Repr()
requires l.Valid() && s.Valid()
requires forall x | x in l.Repr() :: allocated(x)
requires forall x | x in s.Repr() :: allocated(x)
requires {s}+s.Repr()!! {l}+l.Repr()
requires s.Empty()

ensures l.Valid() && old(l.Model())==l.Model()
ensures s.Valid() && s.Model()==Seq.Rev(l.Model())
ensures {s}+s.Repr()!! {l}+l.Repr()

ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
ensures fresh(l.Repr()-old(l.Repr()))
ensures forall x | x in l.Repr() :: allocated(x)

ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() && x !in old(s.Repr()) :: fresh(x)
ensures fresh(s.Repr()-old(s.Repr()))
ensures forall x | x in s.Repr() :: allocated(x)

ensures l.Iterators() >= old(l.Iterators())
{
  var it:=l.Begin();

  assert l.Model() == l.Model()[..|l.Model()|];
  assert Seq.Rev(l.Model()) == Seq.Rev(l.Model()[..|l.Model()|]);
  while(it.HasNext())
  invariant l.Valid()
  invariant it.Valid()
  invariant it.Parent() == l
  invariant l.Size() == old(l.Size())
  decreases l.Size() - it.Index()
  invariant it.Index() <= l.Size()
  invariant l.Iterators() >= old(l.Iterators())
  invariant s.Valid()

  invariant {s}+s.Repr()!! {l}+l.Repr()
  invariant l.Iterators() !! {s}+s.Repr()
  invariant {it} !! {s}+s.Repr()
   
  invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  invariant fresh(l.Repr()-old(l.Repr()))
  invariant forall x | x in l.Repr() :: allocated(x)

  invariant forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() && x !in old(s.Repr()) :: fresh(x)
  invariant fresh(s.Repr()-old(s.Repr()))
  invariant forall x | x in s.Repr() :: allocated(x)
  
  invariant l.Model() == old(l.Model())
  invariant |s.Model()| == it.Index()

  invariant s.Model()==Seq.Rev(l.Model()[..it.Index()]);
  {

      assert s.Model()==Seq.Rev(l.Model()[..it.Index()]);
      var v:=it.Next();
      assert v == l.Model()[it.Index()-1];
      assert l.Model()[..it.Index()-1] + [v] ==l.Model()[..it.Index()];
      s.Push(v);
      Seq.LastRev(l.Model()[..it.Index()-1]+[v]);
      assert [v]+s.Model()[1..] == [v]+ Seq.Rev(l.Model()[..it.Index()-1]) == Seq.Rev(l.Model()[..it.Index()-1]+[v]);
      assert s.Model()==Seq.Rev(l.Model()[..it.Index()]);
  }
}


method fillQueue(l:List, q:Queue)
modifies l,l.Repr(),q, q.Repr()
requires l.Valid() && q.Valid()
requires forall x | x in l.Repr() :: allocated(x)
requires forall x | x in q.Repr() :: allocated(x)
requires {q}+q.Repr()!! {l}+l.Repr()
requires q.Empty()

ensures l.Valid() && old(l.Model())==l.Model()
ensures q.Valid() && q.Model()==l.Model()
ensures {q}+q.Repr()!! {l}+l.Repr()

ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
ensures fresh(l.Repr()-old(l.Repr()))
ensures forall x | x in l.Repr() :: allocated(x)

ensures forall x {:trigger x in q.Repr(), x in old(q.Repr())} | x in q.Repr() && x !in old(q.Repr()) :: fresh(x)
ensures fresh(q.Repr()-old(q.Repr()))
ensures forall x | x in q.Repr() :: allocated(x)

ensures l.Iterators() >= old(l.Iterators())
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
  invariant q.Valid()
  invariant it in l.Iterators()
  invariant {q}+q.Repr()!! {l}+l.Repr()
  invariant l.Iterators() !! {q}+q.Repr()
  //invariant {it} !! {q}+q.Repr()
  
  invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  invariant fresh(l.Repr()-old(l.Repr()))
  invariant forall x | x in l.Repr() :: allocated(x)

  invariant forall x {:trigger x in q.Repr(), x in old(q.Repr())} | x in q.Repr() && x !in old(q.Repr()) :: fresh(x)
  invariant fresh(q.Repr()-old(q.Repr()))
  invariant forall x | x in q.Repr() :: allocated(x)

  invariant l.Model() == old(l.Model())
  invariant q.Model()==l.Model()[..it.Index()]
  {
      var v:=it.Next();
      q.Enqueue(v);
  }
}



method palindrome(l:List,s:Stack,q:Queue) returns (b:bool)
modifies l,l.Repr(), s, s.Repr(), q, q.Repr()
requires l.Valid() && s.Valid() && q.Valid()
requires forall x | x in l.Repr() :: allocated(x)
requires forall x | x in s.Repr() :: allocated(x)
requires forall x | x in q.Repr() :: allocated(x)
requires {l}+l.Repr()!! {s}+s.Repr()
requires {l}+l.Repr()!! {q}+q.Repr()
requires {q}+q.Repr()!! {s}+s.Repr()
requires s.Empty() && q.Empty()

ensures l.Valid() 
ensures s.Valid() && q.Valid()

//ensures: write the properties concerning the model and result b
//l is unchanged and b is true iff l is palindrome
ensures old(l.Model())==l.Model()
ensures b <==> l.Model() == Seq.Rev(l.Model())

ensures l.Iterators() >= old(l.Iterators())


ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
ensures fresh(l.Repr()-old(l.Repr()))
ensures forall x | x in l.Repr() :: allocated(x)

ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() && x !in old(s.Repr()) :: fresh(x)
ensures fresh(s.Repr()-old(s.Repr()))
ensures forall x | x in s.Repr() :: allocated(x)

ensures forall x {:trigger x in l.Repr(), x in old(q.Repr())} | x in q.Repr() && x !in old(q.Repr()) :: fresh(x)
ensures fresh(q.Repr()-old(q.Repr()))
ensures forall x | x in q.Repr() :: allocated(x)
{
  fillStack(l,s); 
  fillQueue(l,q); 

  assert s.Model()==Seq.Rev(q.Model()) == Seq.Rev(l.Model());
  assert s.Model() == Seq.Rev(l.Model()[(|l.Model()| - |q.Model()|)..]);
  assert q.Model() == l.Model();
  assert |s.Model()| == |q.Model()| == |l.Model()| == l.Size();
  assert q.Valid();
  assert q.Model() == l.Model()[(|l.Model()| - |q.Model()|)..];
 
  //loop to check that l is palindrome using s and q

  while(!s.Empty() /*&& !q.Empty()*/ && s.Top() == q.Front())
  invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  invariant fresh(l.Repr()-old(l.Repr()))
  invariant forall x | x in l.Repr() :: allocated(x)

  invariant forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() && x !in old(s.Repr()) :: fresh(x)
  invariant fresh(s.Repr()-old(s.Repr()))
  invariant forall x | x in s.Repr() :: allocated(x)

  invariant forall x {:trigger x in l.Repr(), x in old(q.Repr())} | x in q.Repr() && x !in old(q.Repr()) :: fresh(x)
  invariant fresh(q.Repr()-old(q.Repr()))
  invariant forall x | x in q.Repr() :: allocated(x)

  invariant {l}+l.Repr()!! {s}+s.Repr()
  invariant {l}+l.Repr()!! {q}+q.Repr()
  invariant {q}+q.Repr()!! {s}+s.Repr()
  
  invariant l.Valid()
  invariant s.Valid()
  invariant q.Valid()
  invariant |s.Model()| == |q.Model()|
  decreases |s.Model()|, |q.Model()|
  invariant |q.Model()| <= |l.Model()|
  invariant l.Model() == old(l.Model())

  invariant l.Iterators() !! {s}+s.Repr()
  invariant l.Iterators() !! {q}+q.Repr()
  
  invariant l.Iterators() >= old(l.Iterators())

  invariant q.Model() == l.Model()[(|l.Model()| - |q.Model()|)..]
  invariant s.Model() == Seq.Rev(l.Model())[(|l.Model()| - |s.Model()|)..]
  invariant l.Model()[..(|l.Model()| - |q.Model()|)] == Seq.Rev(l.Model())[..(|l.Model()| - |s.Model()|)]

  //invariant forall i | 0<= i< |l.Model()| - |q.Model()| :: l.Model()[i] == Seq.Rev(l.Model())[i];
 

  {
    var sr := s.Pop();
    var sq := q.Dequeue();

  }
  if(s.Empty() && q.Empty()){ 
    assert l.Model() == Seq.Rev(l.Model());
    return true;
  }
  else{ 
    assert exists i :: 0<=i< |l.Model()| && l.Model()[i] != Seq.Rev(l.Model())[i];
    assert l.Model() != Seq.Rev(l.Model());
    return false;
  }

}

