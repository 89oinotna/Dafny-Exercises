//Creado por: Clara Segura
predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

lemma multis(s:seq<int>,c:int,m:int,f:int)
requires 0<=c<=m<=f<=|s|
ensures multiset(s[c..f]) ==multiset(s[c..m])+multiset(s[m..f])
{
  calc=={
    multiset(s[c..f]);
    {assert s[c..f]==s[c..m]+s[m..f];}
    multiset(s[c..m]+s[m..f]);
 }

}

method mMergeSort(a:array<int>, c:int, f:int)//f excluded
decreases f-c
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
//ensures sorted_seg(a,c,f) //you need to prove sortedness property in merge method in order to have this property
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
 if (f>c+1) //at least two elements 
  {
   var m:=(c+f)/2;   

   //First recursive call
   ghost var a1:=a[..];

   mMergeSort(a,c,m);

   assert a[m..f] == a1[m..f]; //Outside [c..m)
   assert multiset(a[m..f]) == multiset(a1[m..f]);

   assert a1[c..f]==a1[c..m]+a1[m..f];
   multis(a[..],c,m,f);
   assert multiset(a[c..f]) == multiset(a1[c..f]);

  //Second recursive call

   ghost var a2:=a[..];

   mMergeSort(a,m,f);
  
   assert a[c..m] == a2[c..m];// Outside [m..f)
   assert multiset(a[c..m]) == multiset(a2[c..m]) == multiset(a1[c..m]);//It has not been modified
   assert multiset(a[m..f]) == multiset(a2[m..f]) == multiset(a1[m..f]);
   multis(a[..],c,m,f);
   assert multiset(a[c..f])==multiset(a1[c..m])+multiset(a1[m..f]);

   //Merge both halves
   ghost var a3:=a[..];
   mMerge(a,c,m,f);
   assert multiset(a[c..f])==multiset(a3[c..f]);
  } 
}
method {:timeLimitMultiplier 2} mMerge(v:array<int>,c:int,m:int,f:int)
 modifies v
 requires 0<=c<=m<=f<=v.Length
 //requires sorted_seg(v,c,m) && sorted_seg(v,m,f) //You need this to prove mergesort is correct
 //ensures sorted_seg(v,c,f)
 ensures multiset(v[c..f])==multiset(old(v[c..f]))
 ensures v[..c]==old(v[..c]) && v[f..]==old(v[f..])
 {
 var i:=c;
 var j:=m;
 var k:=0;
 var mezcla:=new int[f-c];
 while (i<m && j<f)
   invariant c<=i<=m && m<=j<=f
   invariant k == (i-c)+(j-m) && 0<=k<=f-c
   //invariant //add sortedness properties
   invariant multiset(mezcla[0..k]) == multiset(v[c..i]+v[m..j])
   invariant multiset(v[c..f])==multiset(old(v[c..f]))
   invariant v[..c]==old(v[..c]) && v[f..]==old(v[f..])
   decreases (m-i+f-j)
 {
   if (v[i]<=v[j])
   {
    mezcla[k]:=v[i];
	i:=i+1;
   }
   else 
   {mezcla[k]:=v[j];
    j:=j+1;
    }
	k:=k+1;
 }
 
 while (i<m)
    decreases v.Length-i
    invariant c<=i<=m && m<=j<=f
    invariant k == (i-c)+(j-m) && 0<=k<=f-c
    //invariant //add sortedness properties
    invariant multiset(mezcla[0..k]) == multiset(v[c..i]+v[m..j])
    invariant multiset(v[c..f])==multiset(old(v[c..f]))
    invariant v[..c]==old(v[..c]) && v[f..]==old(v[f..])
 {  mezcla[k]:=v[i];
    i:=i+1;
    k:=k+1;}

 
 while (j<f)
    decreases f-j
    invariant m<=j<=f
    invariant k == (i-c)+(j-m)
    //invariant //add sortedness properties
    invariant multiset(mezcla[0..k]) == multiset(v[c..i]+v[m..j])
    invariant multiset(v[c..f])==multiset(old(v[c..f]))
    invariant v[..c]==old(v[..c]) && v[f..]==old(v[f..])
 {
   mezcla[k]:=v[j];
   j:=j+1;
   k:=k+1;
 }
 assert i==m && j==f;
 assert multiset(mezcla[0..f-c])==multiset(v[c..m]+v[m..f]);
 assert v[c..m]+v[m..f]==v[c..f];
 assert multiset(old(v[c..f]))==multiset(mezcla[0..f-c]);
 //assert sorted_seg(mezcla,0,f-c);

 var l:=0;//copy back the elements
 while (l<f-c)
  decreases f-c-l
  invariant 0<=l<=f-c
  invariant mezcla[0..l]==v[c..l+c]
  invariant multiset(old(v[c..f]))==multiset(mezcla[0..f-c])
  invariant v[..c]==old(v[..c]) && v[f..]==old(v[f..])
  //invariant //add sortedness properties
  { v[l+c]:=mezcla[l]; 
    l:=l+1;
  }

  assert  mezcla[0..f-c]==v[c..f];
  //assert sorted_seg(mezcla,0,f-c);
  //sorted(mezcla,v,c,f);
  //assert sorted_seg(v,c,f);
  
 }


lemma sorted(mezcla:array<int>,v:array<int>,c:int,f:int)
requires 0<=c<=f<=v.Length
requires mezcla.Length==f-c
requires mezcla[0..f-c]==v[c..f]
requires sorted_seg(mezcla,0,f-c)
ensures sorted_seg(v,c,f)
{}