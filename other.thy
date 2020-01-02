theory continuous imports topological_space   begin


definition 
  countable :: "'a set \<Rightarrow> bool" where
  "countable A  \<longleftrightarrow> ( \<exists>f. (f: A \<rightarrow>   Nat) \<and> (inj_on f A) )"

lemma lema_2 : "\<exists>f. ( f : A \<rightarrow>  Nat  \<and>   inj_on f A )  \<Longrightarrow>   countable A"
apply (simp add: countable_def)
done
(*
lemma lema_1 : "\<exists>f. ( f : Nat \<rightarrow> A   \<and>   surj f  )  \<Longrightarrow>   countable A"
apply (simp add: countable_def)
apply simp+
apply blast
done
*)


definition (in topological_space)
  countable_neighborhood_base ::  "'a set set \<Rightarrow> 'a \<Rightarrow>bool"  where
  "countable_neighborhood_base CNB x  \<longleftrightarrow> (neighborhood_base CNB x ) \<and> (countable CNB) "

definition (in topological_space)
   countable_base :: " 'a set set \<Rightarrow> bool"  where
  "countable_base S == base S \<and> countable S" 

definition (in topological_space)
 first_axiom_countability :: "bool" where
 "first_axiom_countability == \<forall>x\<in>X. \<exists>CNB \<subseteq> (neighborhood_system x ). countable_neighborhood_base CNB x "

definition (in topological_space)
 second_axiom_countability :: "bool" where
 "second_axiom_countability == \<exists>S. countable_base S"

definition 
 covering ::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
 "covering A B \<longleftrightarrow>  B \<subseteq>  \<Union>A "

definition 
 countable_covering :: "'a set set \<Rightarrow>'a set \<Rightarrow> bool" where
 "countable_covering A B \<longleftrightarrow> (covering A B) \<and> countable A"

definition (in topological_space)
 open_covering  :: "'a set set \<Rightarrow>'a set \<Rightarrow> bool" where
 "open_covering A B  \<longleftrightarrow> (covering A B) \<and> (\<forall>x\<in> A. open_set x )   "

definition (in topological_space)
 closed_covering  :: "'a set set  \<Rightarrow> bool" where
 "closed_covering A  \<longleftrightarrow> (covering A X) \<and> (\<forall>x\<in> A. closed_set x )   "

(*
locale T0_Space = topology +
  assumes t0 : "\<And> x1 x2. \<lbrakk>x1\<in> X; x2\<in> X; x1\<noteq> x2; neighborhood U x1\<rbrakk>\<Longrightarrow>  x2 \<notin> U "
*)

locale T1_space = topological_space +
  assumes t1 : "!! x1 x2. [|x1: X; x2: X; x1 ~= x2 |]
                ==> EX U V. (neighborhood U x1)  &
                            (neighborhood V x2)  &
                             x2 ~: U &
                             x1 ~: V "
lemma (in T1_space) "x:X ==> closed_set {x}"
apply (simp add :closed_set_def open_set_def)
apply (auto simp: t1
done

(*locale T1_space = topological_space +
  assumes t1 : "\<And> x1 x2. \<lbrakk>x1\<in> X; x2\<in> X; x1\<noteq> x2\<rbrakk>\<Longrightarrow> \<exists>U V. (neighborhood U x1)\<and> (neighborhood V x2) \<and>   x2 \<notin> U \<and> x1 \<notin> V "
*)

locale T2_space = topological_space +
  assumes t2 : "\<And> x1 x2. \<lbrakk>x1\<in> X; x2\<in> X; x1\<noteq> x2\<rbrakk>\<Longrightarrow> \<exists>U V. (neighborhood U x1)\<and> (neighborhood V x2) \<and>   U \<inter>  V ={}"

locale regular_space = T1_space +
  assumes t3 : "\<lbrakk> closed_set F ; p \<in> X ; p \<notin> F  \<rbrakk> \<Longrightarrow> \<exists> U V. (open_set U)\<and> (open_set V) \<and> p \<in> U \<and> F \<subseteq> V \<and> U \<inter> V={}  "

locale normal_space = T1_space +
  assumes ns: "\<lbrakk> closed_set F; closed_set G ; F \<inter> G ={} \<rbrakk> \<Longrightarrow> \<exists>U V. (F \<subseteq> U)\<and> (G \<subset> V)\<and> (U \<inter> V={})  "





   




locale lindeloff_space = topological_space +
  assumes L1:"open_covering A X \<longrightarrow> countable_covering A X"

lemma "lindeloff_space T X \<longrightarrow> topological_space T X"
apply (simp add: lindeloff_space_def)

done
(*
lemma nat_infinite : "infinite EVEN" 
apply (simp add: EVEN_ODD_infinite)
done
*)
lemma countable_sub : "\<lbrakk> countable S ; A \<subseteq> S;infinite A\<rbrakk> \<Longrightarrow> countable A"
apply (simp add:countable_def inj_on_def)
apply done


(*
lemma (in topological_space) Lindeloff [simp,intro] :
   assumes a1 : "A \<subseteq> X"
   and     a2 : "open_covering C A"
   and     a3 : "countable_base S"
   and     a4 : "M={F. \<exists>x\<in>C. F\<subseteq> S \<and>   \<Union>F=x}"
   shows "\<exists>B \<subseteq> C. countable_covering B A "
proof-
  from a2 have b :  "\<forall>x\<in>C. x\<in>T  "  apply (simp add:open_covering_def open_set_def) done 
  from a1 a2 a3  b  have c : "\<forall>x\<in>C. \<exists>F\<subseteq> S. \<Union>F=x "  apply(simp add:countable_base_def base_def ) done 
  from a4  have d:  "\<forall>m\<in>M. m \<subseteq> S "  apply simp  done 
  from a4 d have e: "\<Union>M \<subseteq> S "  apply blast  done
  from e d a4 have f: "countable (\<Union>M)  "
       apply (unfold countable_def) 
       apply (unfold inj_on_def)
       apply (unfold Nat_def)
       apply (unfold lfp_def)
       sorry
*)
  
  end