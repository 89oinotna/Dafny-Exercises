include "ExerciseExp.dfy"

function factorial(n:int):int
    decreases n
	requires n >= 0
	ensures factorial(n)>0
{
if n == 0 then 1 else n*factorial(n-1)
}

lemma  factorial_Lemma(n:int)
    decreases n
	requires n >= 7
	ensures exp(3,n) < factorial(n)
{
	if n==7 {
		assert exp(3,7)<factorial(7);
	}
	else {
		calc {
			
			exp(3,n)<factorial(n);
			== {
				assert n>7;
				assert factorial(n-1)>0;
			}
			exp(3,n-1)*3<factorial(n-1)*n;
		}
	}
}

lemma exp_g_lemma(n:int, e:int)
requires n>=1;
requires e>=1;
ensures exp(n, e) <= exp(n+1, e)
{}

lemma fact_Lemma(n:int)
    decreases n
	requires n >= 1
	ensures factorial(n) <= exp(n,n)
{
	if n==1{
		assert factorial(1) <= exp(1,1);
	}
	else{
		calc{
			factorial(n) ;
			== 
			factorial(n-1) * n;
			<=
			{ fact_Lemma(n-1); }
			exp(n-1,n-1) * n;
			<={
				assert exp(n-1, n-1) >= 1;

				exp_g_lemma(n-1, n-1);
				assert exp(n-1, n-1) <= exp(n,n-1);
			}
			exp(n,n-1) * n;
			==
			exp(n,n);
		}
	}
}