predicate sorted_seg(a:seq<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= |a|
//reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}



method mpartition2(v:array<int>, c:int, f:int, e:int) returns (p:int,q:int)
 modifies v
 requires 0<=c<=f<=v.Length-1 //There is at least one element
 requires e in v[c..f+1] 
 ensures p<=q
 ensures c<=p<=q<=f 
 ensures (forall u::c<=u<p ==> v[u]<e)   && 
         (forall u::p<=u<=q ==> v[u]==e) &&
         (forall w::q+1<=w<=f ==> v[w]>e)
 ensures multiset(v[c..f+1])==multiset(old(v[c..f+1]))
 ensures v[..c]==old(v[..c])
 ensures v[f+1..]==old(v[f+1..])
 //Implement and verify
 {
     assert e in multiset(v[c..f+1]);
 var i,j:=c,f;
 p:=i;
 while (i<=j)
 decreases j-i
 invariant c<=p<=i//<=j+1
 invariant i-1<=j<=f
 invariant c<=i<=j+1<=f+1
 invariant (forall u::c<=u<p ==> v[u]<e)   && 
         (forall u::p<=u<i ==> v[u]==e) &&
         (forall w::j+1<=w<=f ==> v[w]>e)
 invariant multiset(v[c..f+1])==multiset(old(v[c..f+1]))
 invariant v[..c]==old(v[..c])
 invariant v[f+1..]==old(v[f+1..])
 {
    if (v[i]<e) {
        v[p],v[i]:=v[i],v[p];
        i:=i+1;
        p:=p+1;
    }
    else if(v[i] == e){
        i:=i+1;   
    }
    else if (v[j]>e) {j:=j-1;}
    else{
        v[i],v[j]:=v[j],v[i];
        j:=j-1;
    }
}
  q:=i-1;
assert e in multiset(v[c..f+1]) ;
assert p<i;
 }

//Verify quicksort
method {:timeLimitMultiplier 2} quicksort (a:array<int>, c:int, f:int)//c and f included
modifies a 
requires 0 <= c <= f+1 <= a.Length //when c==f+1 empty sequence
ensures sorted_seg(a[..],c,f) 
ensures multiset(a[c..f+1]) == old(multiset(a[c..f+1]))
ensures a[..c]==old(a[..c])
ensures a[f+1..]==old(a[f+1..])
decreases f-c
{
    if (c < f) {
       var p,q := mpartition2(a,c,f,a[c]);
              ghost var a1 := a[..] ; 
        assert sorted_seg(a[..], p,q);

       assert forall k,l::c<=k<p && p<=l<q ==> a[k] < a[l];
        assert multiset(a[c..f+1]) == old(multiset(a[c..f+1]));
       
       quicksort(a,c,p-1);

        assert multiset(a[c..p])==multiset(a1[c..p]);
        assert a[p..] == a1[p..];
            assert a[p..f+1]==a1[p..f+1];
            seqSplit(a[..],c,p,f);
            seqSplit(a1,c,p,f);
            assert multiset(a[c..f+1])==multiset(a1[c..f+1]);

            //Sorting part: left half sorted and pivot still greater

             assert multiset(a[c..p]) == multiset(a1[c..p]);

             multisetPreservesSmaller(a1,a[..],c,p-1,a[p]);
       assert sorted_seg(a[..], c,q);
             ghost var a2 := a[..] ; 
            
       quicksort(a,q+1,f);

    assert multiset(a[q+1..f+1])==multiset(a2[q+1..f+1]);
            assert a[c..q+1]==a2[c..q+1];
            seqSplit(a[..],c,q+1,f);
            seqSplit(a2,c,q+1,f);
            assert multiset(a[c..f+1])==multiset(a2[c..f+1]);
        
        //Sorting part
            assert multiset(a[q+1..f+1]) == multiset(a2[q+1..f+1]);
        assert 0<=p+1<=f+1;
        multisetPreservesGreater(a2,a[..],q+1,f,a[p]);
           
    }
}

lemma multisetPreservesSmaller (a:seq<int>, b:seq<int>, c:int, f:int, x:int)
requires |a|==|b| && 0 <= c <= f + 1 <= |b| 
requires (forall j :: c <= j <= f ==> a[j] <= x)
requires multiset(a[c..f+1]) == multiset(b[c..f+1])
ensures (forall j :: c <= j <= f ==> b[j] <= x)
//Prove this
{

       forall j | c<=j<=f 
       ensures b[j]<=x{
             assert  multiset(a[c..f+1]) == multiset(b[c..f+1]);    
             assert forall k::c<=k<=f ==> b[k] in multiset(a[c..f+1]);
       }
}



lemma multisetPreservesGreater (a:seq<int>, b:seq<int>, c:int, f:int, x:int)
requires |a|==|b| && 0 <= c <= f + 1 <= |b| 
requires (forall j :: c <= j <= f ==> a[j] >= x)
requires multiset(a[c..f+1]) == multiset(b[c..f+1])
ensures (forall j :: c <= j <= f ==> b[j] >= x)
//Prove this
{
       forall j | c<=j<=f 
       ensures b[j]>=x{
             assert  multiset(a[c..f+1]) == multiset(b[c..f+1]);    
             assert forall k::c<=k<=f ==> b[k] in multiset(a[c..f+1]);
       }
}



lemma seqSplit(s:seq<int>, c:int, p:int, f:int)//f excluded
requires 0<=c<=p<=f+1<=|s|
ensures multiset(s[c..f+1])==multiset(s[c..p])+multiset(s[p..f+1])
//Prove this
{
forall s : seq<int>,i,j,k | 0<=i<=k<=j<=|s|
    ensures multiset(s[i..k])+multiset(s[k..j])==multiset(s[i..j])
    {assert s[i..k]+s[k..j]==s[i..j];}
}
 

