theory kuratowski imports topological_space   begin
locale kuratowski_closure  =
 fixes   X  :: "'a set" (structure)
 and     kc :: "'a set  \<Rightarrow> 'a set"
 assumes k0 : "kc \<in> (Pow X) \<rightarrow> (Pow X)"
 and     k1 : "kc {} = {}"
 and     k2 : "\<lbrakk> A \<in> Pow  X \<rbrakk> \<Longrightarrow> ( A \<subseteq> (kc A))"
 and     k3 : "\<lbrakk> A \<in> Pow  X ; B \<in> Pow X\<rbrakk> 
                \<Longrightarrow> kc(A \<union> B) = (kc A) \<union> (kc B)"
 and     k4 : "\<lbrakk> A \<in> Pow  X \<rbrakk> \<Longrightarrow> kc( kc(A)) = kc(A)"

lemma Un_absorb3 : "A \<union>  B = B \<Longrightarrow>  A \<subseteq> B"
apply blast
done
(*
lemma  (in kuratowski_closure) kc_subset_1:
assumes a1: "A \<subseteq> X"
and     a2: "A\<subseteq> B"
shows   "(kc A) \<subseteq> (kc B)"
proof-
from a2 have s1:"B = A\<union> B" apply blast done
from s1 have s2: "(kc B) = kc (A \<union>  B)"  apply simp done
from a1 a2 have s3 : "B \<subseteq> X" apply blast  done 
from a1 a2 have s3: "kc(A \<union> B) = (kc A) \<union> (kc B)" apply (rule k3) done
*)

lemma (in kuratowski_closure) kc_subset:
    "\<lbrakk> B \<subseteq>  X; A \<subseteq> B \<rbrakk> \<Longrightarrow> (kc A) \<subseteq>  (kc B) "

apply(rule_tac A="kc A" and B="kc B" in Un_absorb3)
apply(subgoal_tac "kc B = kc (A \<union> B)")
apply(simp add: k3)
apply(drule Un_absorb1)
apply (drule Un_absorb1)
apply simp
done

lemma (in kuratowski_closure) lemma_k1[intro,simp]: 
     "\<lbrakk> A \<in> Pow X\<rbrakk>  \<Longrightarrow> ( ( kc A) \<in>( Pow X ))"
apply (subgoal_tac "kc \<in> (Pow X) \<rightarrow> (Pow X)")
apply (simp add:Pi_def k0)
apply  (simp add:k0) 
done

(*
lemma (in kuratowski_closure) lemma_k2[intro,simp]:  "\<lbrakk> A \<subseteq>  X\<rbrakk>  \<Longrightarrow> ( ( clos A) \<subseteq>  X )"

apply (rule lemma_k1)

proof-
  assume a: "A \<subseteq> X"
  show  "clos A \<subseteq> X"
  proof 
    from a have b: "A \<in> Pow X"  apply simp done
    from b have "clos A \<in> Pow X" apply (rule lemma_k1) done 
    from b show ?thesis .. 


apply (subgoal_tac "clos \<in> (Pow X) \<rightarrow> (Pow X)")
apply (simp add:Pi_def)
apply  simp 
done
*)

(**)
lemma cl_0[intro,simp]: 
    "T = {t. t \<subseteq> X } \<Longrightarrow> T \<subseteq>  Pow X"
apply (auto simp:Pow_def)
done

lemma (in kuratowski_closure)  cl_1 [intro,simp]:
   "\<lbrakk> T= {t. t\<subseteq> X \<and>  kc( X- t) =(X- t)  } \<rbrakk> \<Longrightarrow>  T \<subseteq> Pow X" 
apply (auto simp:cl_0)
done
   
lemma (in kuratowski_closure) cl_2 [intro,simp]:
   "\<lbrakk> T= {t. t\<subseteq> X \<and> kc(X- t) =(X- t) } \<rbrakk> \<Longrightarrow>  {} \<in> T "
apply  (subgoal_tac "kc X = X")
apply simp
apply (subgoal_tac "kc X \<subseteq> X")
apply  (subgoal_tac "X \<subseteq> kc X")
apply  (simp )
apply simp 
apply (subgoal_tac "kc X \<in> Pow  X") 
apply simp
apply (subgoal_tac "X \<in> Pow X") 
apply simp+
apply (rule lemma_k1)
apply simp 
apply blast 
done



lemma (in kuratowski_closure) cl_3 [intro,simp]:
   "\<lbrakk> T= {t. t\<subseteq> X \<and> kc (X-t) =(X- t)} \<rbrakk> \<Longrightarrow> X\<in> T"
apply  (subgoal_tac "kc {} = {}")
apply simp+
done

 
lemma (in kuratowski_closure)cl_4_0 [intro,simp]:
   assumes a :"T = {t. t\<subseteq> X \<and> kc (X- t) = X- t}" and b: " x\<in> T \<and>  y\<in> T"
   shows "x \<inter> y \<in> T"
proof- 
  from a  b have c : "kc (X-x)=X-x \<and> kc (X-y)=X-y "  apply simp done
  have d: " X-(x \<inter> y)  = (X-x) \<union> (X-y) " apply blast done
  from d have e: "kc (  X-(x \<inter> y) ) = kc((X-x) \<union> (X-y))" apply simp  done
  from a b have f:"x \<in> Pow X \<and> y \<in> Pow X" apply simp done
  from f have g: "X-x \<in> Pow X \<and> X-y \<in> Pow X"  apply (blast) done
  from g have i: "kc ((X-x)\<union> (X-y) ) = kc(X-x) \<union> kc(X-y)" apply (simp add:k3) done
  from  c have j: "kc(X-x) \<union> kc(X-y) = (X-x) \<union> (X-y)"  apply simp done 
  have k:  "(X-x) \<union> (X-y) = X-(x \<inter> y) " apply blast done
  from e  i j k have l: "kc (  X-(x \<inter> y) ) = X-( x\<inter> y) " apply simp done 
  from a b l  have n1:  "x \<inter> y \<in> T" apply blast done
  from n1 show  "x \<inter> y \<in> T "  apply simp done
qed


lemma (in kuratowski_closure)cl_4 [intro,simp]:
 "\<And>x y. \<lbrakk> T= {t. t\<subseteq> X \<and> kc (X- t) = X- t}; x\<in> T ; y\<in> T\<rbrakk> \<Longrightarrow>  x \<inter> y \<in> T"
apply (rule_tac T=T and x=x and y=y in cl_4_0)
apply simp+
done


lemma(in kuratowski_closure)cl_5_0[intro,simp]:
  assumes a:" B\<subseteq> X " 
      and b: "A\<subseteq> B" 
      and c: "C = B - A"
  shows "kc A \<subseteq> kc B"
proof-
  from b c have d: "B=A \<union> C" apply blast done
  from d have e: "kc B = kc (A \<union> C)" apply simp done
  from a b   have f1: "A \<subseteq>  X"  apply simp done
  from a c have f2 : "C \<subseteq> X" apply blast done
  from f1 f2 have g: "kc(A \<union> C)= (kc A ) \<union> (kc C)"   apply simp done
  from e g have i: "kc B = (kc A) \<union> (kc C)" apply simp done 
  from i have j: "kc A \<subseteq> kc B"  apply blast done
  from j show ?thesis apply blast done
qed

lemma(in kuratowski_closure)cl_5_1[intro,simp]:
 "\<lbrakk> B\<subseteq> X; A \<subseteq> B\<rbrakk> \<Longrightarrow> kc A \<subseteq> kc B "
apply simp 
done


lemma (in kuratowski_closure)cl_5_2[intro,simp]:
  assumes a1 :"T = {t. t \<subseteq> X \<and> kc (X- t) =X- t}" 
      and a2 : "M \<subseteq> T"
      and a3 : "U=\<Union>M"
      and a4 : "A \<in> M"
      and a5 : "U'=X - U"
      and a6 : "A' = X - A"
  shows "kc U' \<subseteq>  A'"
proof-
   from a3 a4 a5 a6 have b :"U'\<subseteq> A'" apply blast done
   from a2 a2 b a5 a6 have c : "A'\<subseteq> X" apply blast done
   from b c have c : "kc U' \<subseteq> kc A'" apply simp done
   from  a2  a4 have d: "A \<in> T" apply blast done
   from  a1 d a6 have e: "kc A' = A'" apply simp done
   from c  e show ?thesis apply simp done  
qed

lemma(in kuratowski_closure)cl_5_3[intro,simp]:
"\<And>A.  \<lbrakk> T = {t. t\<subseteq> X \<and> kc (X-t)=X-t}; M\<subseteq> T ; A \<in> M\<rbrakk> \<Longrightarrow> kc ( X - \<Union>M)  \<subseteq> X- A "
apply simp
done

lemma (in kuratowski_closure)cl_5_4[intro,simp]:
  assumes a1 :"T = {t. t \<subseteq> X \<and> kc (X- t) =X- t}" 
      and a2 : "M \<subseteq> T"
      and a3 : "U=\<Union>M"
      and a4 : "L={a'.\<exists>a\<in>M. a'=X-a}"
      and a5 : "A'\<in> L"
     (* and a6 : "A = X-A'"*)
  shows " (X-A') \<in> M"
proof-
   from a1 a2 a3 a4 a5  have b :"\<exists>a \<in> M. A'=X-a " apply simp done 
   from b have c : "\<exists>a\<in>M.  X-A' = X -(X-a) " apply blast done
   from a1 a2 have d : "\<forall>a\<in>M. a\<subseteq> X " apply blast done
   from d have e: "\<forall>a\<in>M. a = X-(X-a)"  apply blast done
   from c e have f: "\<exists>a\<in>M. X-A' = a  " apply simp done
   from e f show ?thesis apply blast done
qed
 
  
lemma(in kuratowski_closure)cl_5_5[intro,simp]:
"\<And>A'. \<lbrakk> T = {t. t\<subseteq> X \<and> kc (X-t)=X-t}; M\<subseteq> T ;L={a'.\<exists>a\<in>M. a'=X-a }; A'\<in>L \<rbrakk> \<Longrightarrow>  (X-A')\<in> M"
apply blast
done

lemma (in kuratowski_closure)cl_5_6[intro,simp]:
  assumes a1 :"T = {t. t \<subseteq> X \<and> kc (X- t) =X- t}" 
      and a2 : "M \<subseteq> T"
      and a3 : "U=\<Union>M"
      and a4 : "L={a'.\<exists>a\<in>M. a'=X-a}"
      and a5 : "A'\<in> L"
     (* and a6 : "A = X-A'"*)
      and a7 : "U' = X-U"
  shows "kc U' \<subseteq>  A'"
proof-
   from a1 a2 a3 a4 a5  a7  have b :" (X-A') \<in> M " apply simp done   
   from a1 a2 a3 a4 a5  a7 b have c : "U' \<subseteq> A'" apply blast done
   from a1 a2 a3 a4 a5  a7 b c have d :" A' \<subseteq> X "  apply blast done
   from c d have e: "kc U' \<subseteq> kc A' " apply auto done
   from b a2 have f: "X -A' \<in> T" apply blast done
   from  f d  have g: "A' = X- (X-A')" apply blast done 
   from a1  f g have i : "kc (X - (X-A')) = X-(X-A')" apply blast done
   from g i have j: "kc A' = A'" apply simp done
   from e j show ?thesis apply blast done
qed

lemma(in kuratowski_closure)cl_5_7[intro,simp]:
"\<And>A'. \<lbrakk> T = {t. t\<subseteq> X \<and> kc (X-t)=X-t}; M\<subseteq> T ;L={a'.\<exists>a\<in>M. a'=X-a }; A'\<in>L  \<rbrakk> \<Longrightarrow>  kc (X-\<Union>M ) \<subseteq> A' "
apply simp 
done 
   
lemma cl_5_8[intro,simp]:
"\<lbrakk>\<And>A. A \<in> C \<Longrightarrow>  B \<subseteq> A\<rbrakk> \<Longrightarrow> B \<subseteq> \<Inter>C "
apply blast
done

lemma cl_5_9[intro,simp]:"\<lbrakk> A \<subseteq> Pow X \<rbrakk> \<Longrightarrow> \<Union>A =X- \<Inter>{a'. \<exists> a\<in> A.  a'=X-a}"
apply blast
done
(*
lemma cl_5_10[intro,simp]:"\<lbrakk> A \<subseteq> Pow X \<rbrakk> \<Longrightarrow> \<Inter>{a'. \<exists> a\<in> A.  a'=X-a}= X - \<Union>A  "
apply blast
*)
(*
lemma Inter_lower: "B \<in> A ==> Inter A \<subseteq> B"
  by blast

lemma Inter_subset2:
  "[| !!X. X \<in> A ==> X \<subseteq> B; A ~= {} |] ==> \<Inter>A \<subseteq> B"
apply (simp add:Inter_subset)
done
*)
(*
lemma "\<not> A \<noteq> {} \<Longrightarrow> A ={}"
apply simp
done
*)


lemma (in kuratowski_closure)cl_5_10[intro,simp]:
  assumes a1 :"T = {t. t \<subseteq> X \<and> kc (X- t) =X- t}" 
      and a2 : "M \<subseteq> T"
      and a3 : "L={a'.\<exists>a\<in>M. a'=X-a}"
  shows " \<Union>M \<in> T "
proof-
  from a1 a2 a3 have b: "\<And>A'.  A'\<in> L \<Longrightarrow> kc (X-\<Union>M) \<subseteq> A' "apply (simp add:cl_5_7) done
  then have c: "kc (X - \<Union>M) \<subseteq> \<Inter>L "  apply (simp add:cl_5_8) done
  from a1 a2 a3 have d : "M \<subseteq> Pow X" apply blast done
  from a1 a3  d  have e: "\<Union>M =X - \<Inter>L  " apply (simp add:cl_5_9) done
 (* from a1 a2 a3 d e  have "L ={} \<Longrightarrow> M ={}"  apply auto done *)
  from a1 a2 a3 d  have f: "\<forall>a. a \<in> M \<Longrightarrow>  a \<subseteq>  X  " apply blast done
  from f have g: "\<forall>a. a\<in>M \<Longrightarrow> X-a \<subseteq> X   "  apply blast done
  have i : " kc ( X - \<Union>M) = X-\<Union>M" 
       proof cases
       assume  i1:"L={}"
         from a1 a2 a3 d e i1 have i2: "M={}"  apply auto done
         from i2 have i3 : "\<Union>M = {} "  apply simp done
         from a1 have i4 : "kc X = X"
               apply (subgoal_tac "kc X \<subseteq> X")
               apply  (subgoal_tac "X \<subseteq> kc X")
               apply  simp+
               apply (subgoal_tac "kc X \<in> Pow  X") 
               apply simp
               apply (subgoal_tac "X \<in> Pow X") 
               apply (rule lemma_k1) 
               apply simp+  done
        from i3 have i5 : "X - \<Union>M = X " apply blast done
        from i5 have i6 : "kc(X - \<Union>M ) = kc X" apply simp done
        from i4 i5 i6 have  i7:  "kc (X- \<Union>M) = X -\<Union>M  " apply simp done
        from i7   show ?thesis apply simp done
      next
      assume j1: "\<not> L = {}"
        from j1 have j2 :"L \<noteq> {}"  apply simp done  
        from a1 a2 a3 g have i : "!!a'. a'\<in> L \<Longrightarrow> a' \<subseteq> X "  apply blast done
        from j2 i have j: "\<Inter>L \<subseteq> X "  apply (simp add:Inter_subset) done 
        from j  have k : " X - (X - \<Inter>L) = \<Inter>L"  apply blast done
        from e k have l : "X - \<Union>M = \<Inter>L  " apply simp done
        from l c have m: "kc ( X - \<Union>M)  \<subseteq> X-\<Union>M" apply simp done
        from d have n : "(X- \<Union>M) \<in>  Pow X " apply blast done 
        from n have o : "(X- \<Union>M ) \<subseteq> kc (X -\<Union>M )"apply (simp add:k2) done
        from m o have p: "kc (X - \<Union>M) = (X -\<Union>M ) " apply simp done
        from p show ?thesis apply simp done
      qed 
      from d a1 a2  have q : "\<Union>M \<subseteq> X "  apply blast done
      from a1 i q show  ?thesis apply simp  done
qed



lemma (in kuratowski_closure) cl_5[intro,simp]:
"\<lbrakk>T = {t. t \<subseteq> X \<and> kc(X- t) =X- t}; M \<subseteq> T \<rbrakk> \<Longrightarrow> \<Union>M \<in> T"  
apply ( rule cl_5_10)
apply simp+
done


 
lemma (in kuratowski_closure ) 
   "\<lbrakk> T= {t. t\<subseteq> X \<and> kc(X - t) = X - t} \<rbrakk>
       \<Longrightarrow>  topological_space T X" 

apply (rule topological_space.intro)
\<dots>
done


apply (simp add:cl_1)
apply (simp add:cl_2)
apply (subgoal_tac "kc X \<subseteq> X")
apply (subgoal_tac "X \<subseteq> kc X")
apply (simp )
apply simp 
apply (subgoal_tac "kc X \<in> Pow  X") 
apply simp
apply (subgoal_tac "X \<in> Pow X") 
apply (rule lemma_k1)
apply simp 
apply simp
apply (simp add:cl_3)
apply (rule cl_4_0)
apply simp
apply simp
apply (rule cl_5_10)
apply simp+
done

definition (in kuratowski_closure) 
   T   where
" T =  {t. t\<subseteq> X \<and> kc (X- t) = X- t}"


lemma (in kuratowski_closure)  T_subset_pow :
   " T \<subseteq> Pow X" 
apply (auto simp:Pi_def T_def)
done

lemma (in kuratowski_closure) kc_in_pow :  "\<lbrakk> A \<in> Pow X\<rbrakk>  \<Longrightarrow> ( ( kc A) \<in>( Pow X ))"
apply (subgoal_tac "kc \<in> (Pow X) \<rightarrow> (Pow X)")
apply (simp add:Pi_def)
apply  simp 
done



lemma (in kuratowski_closure) KC_X_eq:
    "kc X = X"
apply (rule subset_antisym )
apply  (rule PowD)
apply   (rule_tac  A =X  in kc_in_pow)
apply (rule Pow_top)
apply (rule k2)
apply (rule Pow_top)
done


lemma (in kuratowski_closure) KC_subset:
  "\<lbrakk> A \<in> Pow X ; B \<in> Pow X ; A \<subseteq> B  \<rbrakk> \<Longrightarrow> (kc A) \<subseteq> (kc B)  "
apply (subgoal_tac "(kc A) \<subseteq> kc (A \<union> B) ")
apply (subgoal_tac "A \<union> B = B")
apply simp
apply (rule  Un_absorb1)
apply assumption
apply (subgoal_tac "(kc A) \<subseteq>  (kc A) \<union> (kc B)")
apply simp
apply (rule  Un_upper1)
done

lemma(in kuratowski_closure) KC_inter:
  "\<lbrakk> A \<in> Pow X ; B \<in> Pow X  \<rbrakk> \<Longrightarrow> (kc (A \<inter> B)) \<subseteq> (kc A) \<inter> (kc B) "
apply auto
done

lemma (in kuratowski_closure) ww:
  "\<lbrakk> p \<in> X\<rbrakk> \<Longrightarrow> kc {p} = {p}"
apply (rule  subset_antisym)
apply auto
done

lemma (in kuratowski_closure) empty_in_T :
   "{} \<in> T "
apply (simp add:T_def)
apply (rule KC_X_eq)
done

lemma (in kuratowski_closure) X_in_T :
   " X\<in> T"
apply (simp add:T_def)
done