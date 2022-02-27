predicate sorted_seg(a:seq<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= |a|
//reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}
method quicksort (a:array<int>, c:int, f:int)//c and f included
modifies a 
requires 0 <= c <= f+1 <= a.Length //when c==f+1 empty sequence
ensures sorted_seg(a[..],c,f) 
ensures multiset(a[c..f+1]) == old(multiset(a[c..f+1]))
ensures a[..c]==old(a[..c])
ensures a[f+1..]==old(a[f+1..])
decreases f-c
{
    if (c < f) {
       var p := mpartition(a,c,f);
       
            ghost var a1 := a[..] ; 
            /*assert (forall u::c<=u<=p ==> a1[u]<=a1[p]) && 
                   (forall w::p+1<=w<=f ==> a1[w]>=a1[p]);
            */
       quicksort(a,c,p-1);
            //Elements part: permutation
              assert multiset(a[c..p])==multiset(a1[c..p]);
              assert a[p..f+1]==a1[p..f+1];
              seqSplit(a[..],c,p,f);
              seqSplit(a1,c,p,f);
              assert multiset(a[c..f+1])==multiset(a1[c..f+1]);

            //Sorting part: left half sorted and pivot still greater

             assert multiset(a[c..p]) == multiset(a1[c..p]);

             multisetPreservesSmaller(a1,a[..],c,p-1,a[p]);
       
             //assert (forall u::c<=u<=p ==> a[u]<=a[p])&&
             //       (forall w::p+1<=w<=f ==> a[w]>=a[p]);
             //assert sorted_seg(a[..],c,p-1);

      

             ghost var a2 := a[..] ; 
            //assert (forall u::c<=u<=p ==> a2[u]<=a2[p])&&
            //        (forall w::p+1<=w<=f ==> a2[w]>=a2[p]);
            // assert sorted_seg(a2,c,p-1);
       quicksort(a,p+1,f);
             //Elements part
             assert multiset(a[p+1..f+1])==multiset(a2[p+1..f+1]);
             assert a[c..p+1]==a2[c..p+1];
             seqSplit(a[..],c,p+1,f);
             seqSplit(a2,c,p+1,f);
             assert multiset(a[c..f+1])==multiset(a2[c..f+1]);
            
            //Sorting part
             assert multiset(a[p+1..f+1]) == multiset(a2[p+1..f+1]);
            assert 0<=p+1<=f+1;
            multisetPreservesGreater(a2,a[..],p+1,f,a[p]);
           // assert (forall w::p+1<=w<=f ==> a[w]>=a[p]);
           // assert sorted_seg(a[..],p+1,f); 

           // assert (forall u::c<=u<=p ==> a[u]<=a[p]);
           // assert sorted_seg(a[..],c,p-1);
           // assert sorted_seg(a[..],c,f);
      
    }
}


method mpartition(v:array<int>, c:int, f:int) returns (p:int)//c and f included
 modifies v
 requires 0<=c<=f<=v.Length-1 //At least one element
 ensures c<=p<=f 
 ensures (forall u::c<=u<=p ==> v[u]<=v[p]) && 
        (forall w::p+1<=w<=f ==> v[w]>=v[p])
 ensures multiset(v[c..f+1])==multiset(old(v[c..f+1]))
 ensures v[..c]==old(v[..c])
 ensures v[f+1..]==old(v[f+1..])
 {
 var i,j:=c+1,f;
 while (i<=j)
  decreases j-i
  invariant c+1<=i<=j+1<=f+1
  invariant (forall u::c+1<=u<i ==> v[u]<=v[c]) &&
            (forall w::j+1<=w<=f ==> v[w]>=v[c])
  invariant multiset(v[c..f+1])==multiset(old(v[c..f+1]))
  invariant v[..c]==old(v[..c])
  invariant v[f+1..]==old(v[f+1..])
 {
   if (v[i]<=v[c]) {i:=i+1;}
   else if (v[j]>=v[c]) {j:=j-1;}
   else {
    v[i],v[j]:=v[j],v[i];
	  i:=i+1;
   	j:=j-1;}
   }
  p:=j;
  v[c],v[p]:=v[p],v[c];
 
 }


lemma multisetPreservesSmaller (a:seq<int>, b:seq<int>, c:int, f:int, x:int)
requires |a|==|b| && 0 <= c <= f + 1 <= |b| 
requires (forall j :: c <= j <= f ==> a[j] <= x)
requires multiset(a[c..f+1]) == multiset(b[c..f+1])
ensures (forall j :: c <= j <= f ==> b[j] <= x)
//Prove this



lemma multisetPreservesGreater (a:seq<int>, b:seq<int>, c:int, f:int, x:int)
requires |a|==|b| && 0 <= c <= f + 1 <= |b| 
requires (forall j :: c <= j <= f ==> a[j] >= x)
requires multiset(a[c..f+1]) == multiset(b[c..f+1])
ensures (forall j :: c <= j <= f ==> b[j] >= x)
//Prove this



lemma seqSplit(s:seq<int>, c:int, p:int, f:int)//f excluded
requires 0<=c<=p<=f+1<=|s|
ensures multiset(s[c..f+1])==multiset(s[c..p])+multiset(s[p..f+1])
//Prove this
