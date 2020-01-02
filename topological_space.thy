theory topological_space imports
  "~~/src/HOL/Library/FuncSet" 
  "~~/src/HOL/Library/Zorn"

begin

(* datatype_new   'a top = "'a set set"*)  


locale topological_space =
  fixes X 
  and T 
  assumes O1[simp]  :  "T \<subseteq>  Pow X"
  and     O2[simp]  :  "{} \<in> T"
  and     O3[simp]  :  "X \<in> T"
  and     O4[simp]  :  "\<lbrakk>x \<in> T ; y \<in> T \<rbrakk> \<Longrightarrow>  x \<inter> y \<in> T"
  and     O5[simp]  :  "\<lbrakk>T1 \<subseteq> T \<rbrakk> \<Longrightarrow>  \<Union>T1  \<in> T"

thm topological_space_def

lemma Un_eq_Union: "A \<union> B = \<Union>{A, B}"
  by blast


thm Un_eq_Union 

lemma  (in topological_space) union_in_T [simp]:
    "\<lbrakk> x \<in> T ; y \<in> T \<rbrakk> \<Longrightarrow> x \<union> y \<in> T"
apply (subst Un_eq_Union)
apply (rule O5)
apply simp
done

lemma (in topological_space) union_in_T2 :
    assumes  a :"x \<in> T \<and>  y \<in>  T"   shows " x \<union>  y \<in>  T"
proof- 
   from a have b:  "{x,y} \<subseteq>  T"  apply simp done  
   from b have c : "\<Union>{x,y} \<in>  T " apply (simp add: O5) done
   have d:  "\<Union>{x,y} = x \<union> y"  apply blast done
   from c d have e: "x \<union> y \<in>  T"  apply simp done
   show ?thesis  apply  (blast intro :e)  done
qed
 
lemma (in topological_space) Un_T_in_T:"\<Union>T \<in> T"
apply (simp add:O5)
done

lemma (in topological_space)  Un_T_eq_X [intro,simp] :
    "\<Union> T =X "
apply (subgoal_tac "T \<subseteq> Pow X")
apply (subgoal_tac "X \<in> T")
apply blast 
apply simp+
done

definition  trivial_topology :: 
  "'a set \<Rightarrow> 'a top" 
      where
  "trivial_topology X = {{}, X} "

lemma trivial_is_top: 
    "topological_space  X (trivial_topology X) "
apply (rule topological_space.intro)
apply (simp add:trivial_topology_def)+
apply blast
apply (simp add:trivial_topology_def)
apply blast
done

definition discrete_topology::
   "'a set \<Rightarrow> 'a top" 
        where
   "discrete_topology X = Pow X"

lemma discrete_is_top:
    "topological_space X (discrete_topology X)"
apply (rule topological_space.intro)
apply (simp add:discrete_topology_def)+
apply blast
apply (simp add:discrete_topology_def)
apply blast
done

lemma (in topological_space)dis_top_1: 
    "\<And>x.\<lbrakk> x\<in> X \<Longrightarrow> {x} \<in> T \<rbrakk> \<Longrightarrow>  T = discrete_topology X"
apply (simp add:discrete_topology_def O3 O4 O5)
apply auto
done

definition
   finer ::"'a top \<Rightarrow> 'a top \<Rightarrow> 'a set  \<Rightarrow> bool "
      where
   "finer T2 T1 X  == topological_space X T1 \<and>
                      topological_space X T2 \<and>
                      T1  \<subseteq> T2"
(*lemma "\<lbrakk> P ;Q\<rbrakk> \<Longrightarrow> P \<and> Q"*)

lemma "finer (discrete_topology X) (trivial_topology X) X "
apply (simp add :finer_def)
apply (rule conjI)
apply (rule trivial_is_top)
apply (rule conjI)
apply(rule  discrete_is_top)
apply (simp add:trivial_topology_def discrete_topology_def)
done

lemma "\<lbrakk> X ={a ,b} ; T ={{}, {a} ,X} \<rbrakk> \<Longrightarrow> topological_space X T"
apply (simp add:topological_space_def)
apply blast
done

thm finite_def

lemma "topological_space X ({A. A \<subseteq> X \<and> finite A } \<union> {{}})"
apply (simp add: topological_space_def)
apply (rule conjI)
apply blast
apply (rule conjI)
apply auto
done

section "open set"

definition  (in topological_space)
   open_set :: " 'a set \<Rightarrow>  bool"  where
  "open_set s  \<longleftrightarrow>  s \<in> T"

lemma "\<lbrakk> topological_space X T; topological_space.open_set T s \<rbrakk> \<Longrightarrow>  (s \<in> T)"
apply (simp add: topological_space.open_set_def)
done


lemma (in topological_space) openI:
  "m \<in>  T \<Longrightarrow> open_set m"
apply (simp add: open_set_def)
done

lemma (in topological_space) openE:
  "\<lbrakk> open_set m; m \<in>  T \<Longrightarrow>  R \<rbrakk>  \<Longrightarrow>  R" 
apply  (auto simp: open_set_def)
done

lemma (in topological_space) empty_is_open:
   "open_set {}"
apply(simp add:open_set_def)
done

lemma (in topological_space) X_is_open:
  "open_set X"
apply (simp add:open_set_def)
done

lemma (in topological_space) union_is_open :
    "\<lbrakk> open_set A ;open_set B \<rbrakk> \<Longrightarrow>  open_set ( A \<union> B)"
apply (simp add:open_set_def)
done

lemma (in topological_space) inter_is_open:
   "\<lbrakk>open_set A ; open_set B \<rbrakk> \<Longrightarrow> open_set (A \<inter> B)"
apply (simp add:open_set_def)
done

lemma (in topological_space) UN_is_open :
   "\<forall>x \<in> T'. open_set x  \<Longrightarrow> open_set  (\<Union> T') "
apply (simp add:open_set_def)
apply (subgoal_tac "T' \<subseteq> T")
apply simp
apply (simp add: subsetI)
done

lemma (in topological_space)
  "[| ALL x : T'. open_set x  |] ==>  open_set ( Union T')"
apply (simp add: open_set_def)
apply (subgoal_tac "T' <= T")
apply simp
apply (simp add: subsetI)
done

lemma subset_pow [intro,simp] :
     "\<lbrakk> T \<subseteq> Pow X ; t \<in> T ; x \<in> t\<rbrakk> \<Longrightarrow> x \<in> X "
apply blast
done

thm subsetI
lemma (in topological_space) openE_in_X [intro,simp]:
  "\<lbrakk> open_set t; x \<in> t \<rbrakk> \<Longrightarrow> x \<in> X"
apply (subgoal_tac "T \<subseteq>   Pow X" "t \<in> T")
apply  blast
apply (simp add :open_set_def)+
done

lemma (in topological_space) open_set_E [elim]:
 "\<lbrakk> x \<in> X; \<And>  t. \<lbrakk>  open_set t; x \<in>  t \<rbrakk>  \<Longrightarrow>  R\<rbrakk>  \<Longrightarrow>  R"
apply (unfold open_set_def)
apply (insert O3)
apply blast
done

lemma (in topological_space)
 "[| x : X; !!  t. [|  open_set t; x :  t |]  ==>  R |]  ==> R"
apply (unfold open_set_def)
apply (insert O3)
apply blast
done
lemma (in topological_space) subE_is_open:
  "[|  t :  M; M <=  T |] ==> open_set t"
 apply  (unfold open_set_def)
apply (rule_tac A="M" in  set_mp)
apply assumption
apply assumption
done

lemma (in topological_space) open_subset_I:
assumes a1: "open_set A"
shows "A \<subseteq> X"
proof-
 from a1 have s1:"A \<in> T" by (simp add:open_set_def)
 from a1 show ?thesis using O1 by blast
qed

lemma (in topological_space) open_subset
:"open_set A \<Longrightarrow> A \<subseteq> X"
apply (simp add:open_set_def )
apply (insert O1)
apply blast
done



section "neighborhood"


definition (in topological_space) neighborhood :: "'a set \<Rightarrow> 'a  \<Rightarrow> bool"  where
  "neighborhood U x == U \<subseteq> X \<and> (\<exists>V \<in> T .x\<in> V \<and> V \<subseteq> U)"

definition (in topological_space)open_neighborhood ::"'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "open_neighborhood  U x == x \<in> U   \<and> U \<in> T"

(*definition (in topological_space)open_neighborhood ::"'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "open_neighborhood  U x ==( neighborhood U x) \<and> U \<in> T"
*)
lemma (in topological_space) inT_subX: "U \<in> T \<Longrightarrow> U \<subseteq> X"
  apply (subgoal_tac "T \<subseteq> Pow X")
  apply (subgoal_tac "U \<in> Pow X")
  apply simp
  apply blast
  apply simp
done
lemma exD:  "\<exists>x . x\<in> T \<and> P x \<Longrightarrow> \<exists>x\<in>T . P x"
apply  blast
done

lemma  (in topological_space)  open_nb_is_nb:
  "open_neighborhood U x  \<Longrightarrow> neighborhood U x "
thm bexI
thm subset_refl
apply (simp add:open_neighborhood_def neighborhood_def)
apply (rule conjI)
apply (drule conjunct2)
(*apply (drule_tac P="x \<in> U "  and  Q="U \<in> T"  in conjunct2*)
  apply (subgoal_tac "T \<subseteq> Pow X")
  apply (subgoal_tac "U \<in> Pow X")
  apply simp
  apply blast
  apply simp
apply (rule exD)
apply (rule_tac x="U" in exI)
apply (rule conjI)
apply (drule conjunct2)
apply assumption
apply (rule conjI)
apply (drule conjunct1)
apply (assumption)
apply simp
done


definition (in topological_space) neighborhood_system :: "'a \<Rightarrow> 'a set set" where
  "neighborhood_system x = { U. (neighborhood U x) }"
definition (in topological_space) open_neighborhood_system ::"'a \<Rightarrow> 'a set set" where
 "open_neighborhood_system x = {U. (open_neighborhood U x)}"
       
(*from GaoGuoShi 8 page*)
lemma (in topological_space) open_nbs_inc:
"U \<in> ( open_neighborhood_system x) \<Longrightarrow> U \<in> (neighborhood_system x) "
apply (unfold open_neighborhood_system_def) 
apply (unfold neighborhood_system_def  ) 
apply (simp add:open_nb_is_nb)
done

lemma (in topological_space) open_nbs_intro:
"\<forall>U \<in> (neighborhood_system x). P U x \<Longrightarrow> \<forall>U\<in> (open_neighborhood_system x). P U x"
apply (insert open_nbs_inc)
apply simp
done


lemma (in topological_space) X_in_nbs:
  "  x\<in> X \<Longrightarrow> X \<in>  neighborhood_system x "
apply ( simp add:neighborhood_system_def) 
apply (simp add:neighborhood_def)
apply (insert O3)
(*thm exI  ?P ?x \<Longrightarrow> \<exists>x. ?P x*)
apply (rule_tac x ="X"   in bexI)
apply (rule conjI)
apply assumption
apply (rule subset_refl)
apply assumption
done

lemma (in topological_space) nbs_in:
  "A \<in> neighborhood_system x \<Longrightarrow> x \<in> A"
apply (simp add:neighborhood_system_def)
apply (simp add:neighborhood_def) 
(*apply (erule_tac P="A \<subseteq> X" and Q="\<exists>V\<in>T. x \<in> V \<and> V \<subseteq> A" in conjI*)
apply blast
done

lemma (in topological_space) nbs_inter:
     "[| A : neighborhood_system x;
         B : neighborhood_system x
      |] ==>  A Int B : neighborhood_system x"

proof -
  assume a1: "A : neighborhood_system x"
    and  a2: "B : neighborhood_system x"
from a1 have s1:" A \<in> T "
         apply (auto simp:neighborhood_system_def neighborhood_def)

apply (simp add:neighborhood_system_def)
apply (simp add:neighborhood_def) 
apply (rule conjI)
apply (drule conjunct1 )
apply (drule conjunct1 )
apply (erule le_infI1)
apply (drule conjunct2)
apply (drule conjunct2)
apply (drule rev_bexI)
done

lemma 
  (in topological_space) nbs_sub_in:
  "\<lbrakk> A \<in> neighborhood_system x; A \<subseteq> B ; B \<subseteq> X \<rbrakk> \<Longrightarrow> B \<in> neighborhood_system x"
apply (simp add:neighborhood_system_def)
apply (simp add: neighborhood_def)
done


lemma (in topological_space) open_nb_ex  :
  "\<lbrakk>open_set A ; x \<in> A \<rbrakk> \<Longrightarrow> \<exists>U. neighborhood U x \<and> U \<subseteq> A"
apply (unfold neighborhood_def)
apply (unfold open_set_def)
apply (frule inT_subX)
apply auto
done

(*  \<lbrakk>A \<subseteq> X; A \<in> T; x \<in> A\<rbrakk> \<Longrightarrow> \<exists>U. (U \<subseteq> X \<and> (\<exists>V\<in>T. x \<in> V \<and> V \<subseteq> U)) \<and> U \<subseteq> A *)

lemma (in topological_space) open_nb_ex_a:
  "\<lbrakk>open_set A \<rbrakk> \<Longrightarrow> \<forall>x\<in> A. \<exists>U. neighborhood U x \<and> U \<subseteq> A  "
apply (auto simp :open_nb_ex)
done

lemma (in topological_space) nbs_open_ex:
  "\<lbrakk>open_set A \<rbrakk> \<Longrightarrow> \<forall>x\<in> A. \<exists>U\<in>neighborhood_system x. U \<subseteq> A  "
apply (auto simp :open_nb_ex_a neighborhood_system_def)
done 

lemma (in topological_space)  x_in_nb :
"\<lbrakk> x\<in> X ; U \<in> neighborhood_system x \<rbrakk> \<Longrightarrow> x \<in> U "
apply ( simp add:neighborhood_system_def) 
apply (simp add:neighborhood_def)
apply blast
done



section "closeed_set"

definition  (in topological_space)
   closed_set :: " 'a set \<Rightarrow>  bool"  where
  "closed_set s  \<longleftrightarrow>  open_set (X - s) \<and> s \<subseteq> X"

(*
definition (in topological_space) closed_set_system :: "'a set set" where
  "closed_set_system = { C. (closed_set C) }"
*)

thm topological_space.closed_set_def
lemma dis_all_is_open: 
    "\<And>x. x \<subseteq> X \<Longrightarrow> topological_space.open_set (discrete_topology X) x 
                \<and>  topological_space.closed_set X (discrete_topology X) x"
apply (insert discrete_is_top[of "X" ])
apply (unfold discrete_topology_def
              topological_space.closed_set_def 
              topological_space.open_set_def)
apply (rule conjI)
apply (rule PowI)
thm PowI
apply assumption
apply (rule conjI)
apply (rule_tac A ="X - x" in  PowI)
apply (rule Diff_subset)
apply assumption

done

lemma dis_all_is_closed : 
   "\<And>x. x \<subseteq> X \<Longrightarrow> topological_space.closed_set X (discrete_topology X) x "
apply (insert discrete_is_top[of "X" ])
apply (unfold discrete_topology_def 
              topological_space.closed_set_def
              topological_space.open_set_def)
apply (rule conjI)
apply (rule_tac A ="X - x" in  PowI)
apply (rule Diff_subset)
apply assumption
done


lemma  (in topological_space) close_sub_X:
    "\<lbrakk> closed_set s\<rbrakk> \<Longrightarrow> s \<subseteq> X"
apply (simp add : closed_set_def open_set_def)
done

lemma (in topological_space) empty_is_closed:
  "closed_set {}"
apply (simp add:closed_set_def)
apply (simp add:open_set_def)
done

lemma (in topological_space) X_is_closed:
 "closed_set X"
apply(simp add:closed_set_def) 
apply(simp add:open_set_def)
done

lemma (in topological_space) closed_Union:
 "\<lbrakk> closed_set A; closed_set B \<rbrakk> \<Longrightarrow> closed_set (A \<union> B)"
apply (simp add:closed_set_def)
apply (simp add:open_set_def)
apply (subst  Diff_Un)
apply (erule_tac P="X - A \<in> T" and Q =" A \<subseteq> X" in  conjE)
apply (erule_tac P="X - B \<in> T" and Q =" B \<subseteq> X" in  conjE)
apply simp
done

(*definition (in topological_space)
  closure :: "' a set \<Rightarrow> 'a set set "
    where
  "closure A \<equiv> \<Inter>{C. A \<subseteq> C \<and> closed_set C}"
*)


(*
lemma (in topological_space) 
assumes a1: "open_set A"
shows "A \<in> neighborhood_system y \<and>  y\<in> A \<and> A \<subseteq> A"
proof-
  from a1 have s1 :"A \<in> neighborhood_sytem y" 
    apply (auto :open_set_def neighborhood_system_def neighborhood_def)

    done



lemma (in topological_space) 
   "open_set A \<Longrightarrow> A \<in> neighborhood_system y \<and>  y\<in> A \<and> A \<subseteq> A"

apply ( simp add:open_set_def neighborhood_system_def neighborhood_def)
apply 
*)
lemma (in topological_space) 
   "open_set A \<Longrightarrow>\<forall>y\<in> A. \<exists> B\<in> neighborhood_system y. y\<in> B \<and> B \<subseteq> A"
apply (simp add:open_nb_ex_a nbs_in neighborhood_system_def)                                        
done

definition (in topological_space)
   cluster_point :: " 'a \<Rightarrow>'a set \<Rightarrow> bool"  where
  "cluster_point x A == A \<subseteq> X  \<and> x \<in> X \<and> (\<forall>U\<in> neighborhood_system  x.  U \<inter> (A -{x}) \<noteq> {}) "


definition (in topological_space)
  derived_set :: "'a set \<Rightarrow> 'a set " where
  "derived_set A == {x. (cluster_point x A)}"

(*lemma "\<lbrakk> P \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> P \<longrightarrow> Q"*)

lemma (in topological_space) empty_mult_is_empty:
  "\<forall>U\<in>neighborhood_system x. U \<inter> ({} - {x}) = {}"
apply simp
done
(*
lemma (in topological_space) d_empty_is_empty:
 "derived_set {} = {}"
apply (unfold derived_set_def) 
apply(unfold cluster_point_def)
apply(auto simp: empty_mult_is_empty)
apply (unfold neighborhood_system_def)
apply (unfold neighborhood_def)
apply auto
apply blast
apply *)
lemma (in topological_space) closed_is_derived_pre:
assumes a1:"closed_set A"
and  a2:"x\<in> derived_set A"
shows "x \<in> A"
       proof-
           have a0:"x \<notin> A\<Longrightarrow>False"
        proof-
          assume a3:"x\<notin> A"
          show "False"
          proof-
          from a2 have s2:"A\<subseteq> X" by (auto simp:derived_set_def cluster_point_def)
          from a2 have s3:"x\<in> X" by (auto simp:derived_set_def cluster_point_def)
          from a2 have s4:"\<forall>U\<in> neighborhood_system  x.  U \<inter> (A -{x}) \<noteq> {}"
                by (auto simp:derived_set_def cluster_point_def)
          from a3 s2 s3 have s5: "x \<in> X - A" by blast
          from a1 s2  have s6: "open_set (X - A)" by (simp add:closed_set_def)
          from s6 have s7:  "\<forall>y\<in> X -A. \<exists> B\<in> neighborhood_system y. y\<in> B \<and> B \<subseteq> X - A " 
                   by (simp add:open_nb_ex_a nbs_in neighborhood_system_def)      
     
          from s5 s7 have s8:"\<exists> B\<in> neighborhood_system x. x\<in> B \<and> B \<subseteq> X - A " by auto
          from s8  obtain B where  s9:"B\<in> neighborhood_system x" and
                                  s10:"x\<in> B" and
                                  s11:"B\<subseteq> X -A" by blast
          from s11 have s12: "B \<inter> A ={}" by blast
          from s12 have s13: "B \<inter>  (A -{x}) ={}" by blast
          from s4 s9 s13 have  s14 :"False" by auto
          from a3 s14 show ?thesis by auto
qed
qed
from a0  show ?thesis by auto
qed


lemma (in topological_space) closed_is_derived:
assumes a1:"closed_set A"
shows "derived_set A \<subseteq> A" 
   proof-
        from a1 have s0:"\<And> x. x \<in> derived_set A \<Longrightarrow> x \<in> A "  
        proof-
        fix x assume a2: "x\<in> derived_set A"
        show s1: "x \<in> A"
        proof-
          from a1 a2 show ?thesis by (auto simp:closed_is_derived_pre)
qed
qed
from s0 show ?thesis by auto
qed


lemma " \<forall> x\<in>A. c\<in> B \<and> P A c x \<Longrightarrow> \<forall>x\<in> A. \<exists> a\<in> B. P A a x "
apply auto
done

lemma (in topological_space)
 "A \<in> T \<Longrightarrow> A \<subseteq> X"
apply (insert O1)
apply blast
done


thm exI
thm ballI
thm ballE

lemma all_Ex: "\<forall> x. P x \<Longrightarrow> \<exists> x. P x"
apply blast
done
(*
lemma "\<exists>a\<in> A. P a"
apply (simp add:Pi)
done
lemma all_ex_1:
assumes a1: "\<forall>x \<in>A. P x"
shows "\<exists>a\<in> A. P a "
proof-
 fix x
 from a1 have s1:"x\<in> A \<longrightarrow> P x" by blast
 from s1 have s2: "\<exists>a\<in> A. P a " by blast

lemma  "\<forall>x \<in>A. P x \<Longrightarrow> \<exists>a\<in> A. P a "
apply (rule_tac  exI)
done
*)
(*
lemma "\<forall>B \<in> x. (C B x) \<Longrightarrow>  B0 \<in> x \<and> (C B0 X)"
apply blast
*)


lemma "\<exists>x\<in>A. (\<forall>B \<in> x. (C B x)) \<Longrightarrow> \<exists>x. x\<in> A \<and> (\<forall>B \<in> x. (C B x))"
apply blast
done

lemma "\<lbrakk> \<exists>x\<in> A. x\<notin> B \<Longrightarrow> False \<rbrakk> \<Longrightarrow>  A \<subseteq> B "
apply blast
done
(*
lemma "\<lbrakk> \<exists>x\<in> A. \<forall>B \<in> (W x).  (F B x) \<Longrightarrow> False \<rbrakk> \<Longrightarrow> \<forall>x\<in> A. \<exists> B \<in> (W x). \<not>(F B X)"
a
done*)
(*
lemma "\<lbrakk>\<exists>x. x \<in> A \<and> (\<forall>B. B \<in> (W x) \<and> (F B X))\<Longrightarrow> False\<rbrakk> \<Longrightarrow> \<forall> x. x \<in> A \<and> (\<exists> B. B \<in> (W x) \<and>  \<not>(F B X)) "
apply blast
done


lemma  "\<lbrakk> \<exists> x\<in> A. \<forall> B\<in> C. x \<in> B \<rbrakk> \<Longrightarrow> \<exists>x. \<forall> B. x\<in>A \<and> B\<in> C \<and> x \<in> B"   
apply simp
apply blast
*)

(*
lemma (in topological_space) derived_is_closed:
assumes a1:"derived_set A \<subseteq> A"
shows "closed_set A"
proof-
  from a1 have s0:"\<exists> x\<in> (X-A). \<forall>B\<in>(neighborhood_system x). B\<inter> A \<noteq> {} \<Longrightarrow> False"
  proof-
     assume a2:"\<exists> x\<in> (X-A). (\<forall>B\<in>(neighborhood_system x). B\<inter> A \<noteq> {})"
     show "False"
     proof-
       from a2 have s1: "\<exists> x. x \<in> (X-A)\<and> (\<forall>B\<in>(neighborhood_system x). B\<inter> A \<noteq> {})" apply auto done
       from s1 obtain x where  s2:" x \<in> (X - A)" and 
                          s3:" \<forall>B\<in>(neighborhood_system x). B\<inter> A \<noteq> {}" apply auto done
       fix B from s3 have s4:"B \<in> (neighborhood_system x) \<longrightarrow>  B\<inter> A \<noteq> {}"
              by blast 
       fix B from a2 have s1:"\<exists> x\<in> (X-A). B\<in>(neighborhood_system x) \<and>  B\<inter> A \<noteq> {}" by blast


obtain x where s1:"x \<in> (X - A)" 
                                 and s2:"B \<in> (neighborhood_system x)"
                                 and s3:"B \<inter> A \<noteq> {}"                    

apply   
"\<lbrakk> derived_set A \<subseteq> A  \<rbrakk> \<Longrightarrow> closed_set A "
apply (unfold closed_set_def)
apply (unfold derived_set_def)
apply (unfold cluster_point_def)
apply (unfold neighborhood_def)
apply (unfold open_set_def)
apply  auto
apply(simp add:closed_set_def open_set_def neighborhood_def derived_set_def cluster_point_def)
apply blast

apply (auto simp:closed_set_def open_set_def neighborhood_def derived_set_def cluster_point_def)

*)


lemma  (in topological_space)
  "\<forall> A\<subseteq> X. closed_set (derived_set A) \<Longrightarrow> \<forall> x\<in> X. closed_set (derived_set {x})"
apply (auto simp :closed_set_def open_set_def derived_set_def)
done

(*
lemma  (in topological_space)
  "\<forall> x\<in> X. closed_set (derived_set {x})\<Longrightarrow> \<forall> A\<subseteq> X. closed_set (derived_set A)"
apply (simp add:closed_set_def open_set_def neighborhood_def derived_set_def cluster_point_def)
apply blast
done
*)

(*lemma in_exI: "\<lbrakk> a\<in>A ; P a \<rbrakk> \<Longrightarrow> \<exists>x\<in>A. P x  "*)

lemma  bsubexI:"\<lbrakk> a \<subseteq> A ; P a \<rbrakk> \<Longrightarrow>\<exists>x\<subseteq>A. P x "
apply blast
done

lemma "\<lbrakk> \<forall>x. A x = B ;\<forall>x. A x \<noteq> B\<rbrakk> \<Longrightarrow> False"

apply blast
done
(*
lemma "\<lbrakk> \<forall>x\<in> C. A x = B ;\<forall>x\<in> C. A x \<noteq> B\<rbrakk> \<Longrightarrow> False"
*)

(*
HOL.contrapos_np: \<lbrakk>\<not> ?Q; \<not> ?P \<Longrightarrow> ?Q\<rbrakk> \<Longrightarrow> ?P
  HOL.contrapos_pp: \<lbrakk>?Q; \<not> ?P \<Longrightarrow> \<not> ?Q\<rbrakk> \<Longrightarrow> ?P
  HOL.notE: \<lbrakk>\<not> ?P; ?P\<rbrakk> \<Longrightarrow> ?R
  HOL.notE': \<lbrakk>\<not> ?P; \<not> ?P \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?R
  HOL.rev_notE: \<lbrakk>?P; \<not> ?R \<Longrightarrow> \<not> ?P\<rbrakk> \<Longrightarrow> ?R
 bexI \<lbrakk>?P ?x; ?x \<in> ?A\<rbrakk> \<Longrightarrow> \<exists>x\<in>?A. ?P x

*)

lemma (in topological_space) nbs_not_empty:
"\<lbrakk> x\<in> X\<rbrakk> \<Longrightarrow> neighborhood_system x \<noteq> {}"
apply(simp add: neighborhood_system_def neighborhood_def)
apply(rule_tac x="X" in exI)
apply(rule conjI)
apply(simp)
apply(rule_tac x="X" in bexI)
apply (rule conjI)
apply assumption
apply simp
apply simp
done

lemma (in topological_space) open_nbs_not_empty:
"\<lbrakk> x\<in> X\<rbrakk> \<Longrightarrow> open_neighborhood_system x \<noteq> {}"
apply (simp add:open_neighborhood_system_def open_neighborhood_def neighborhood_def)
apply (rule_tac x="X" in exI)
apply (rule conjI)
apply assumption
apply simp
done

lemma (in topological_space) sp_notin_dset_pre:
assumes a1: "x \<in>  derived_set {x}"
shows False
proof-
  from a1 have s1:"{x} \<subseteq> X" by (simp add:derived_set_def cluster_point_def)
  from a1 have s2:"x\<in> X"  by (simp add:derived_set_def cluster_point_def)
  from a1 have s3:"\<forall>U\<in> neighborhood_system  x.  U \<inter> ({x} -{x}) \<noteq> {}" 
       by (simp add:derived_set_def cluster_point_def)
  have s4 : "U \<inter> ({x} - {x})={}" by blast
  from  s1 s3 s4 show ?thesis by (simp add:nbs_not_empty) 
qed



lemma (in topological_space) sp_notin_dset:
"x \<notin> derived_set {x}"
apply (rule_tac Q="False" in contrapos_np)
apply simp+
apply (rule_tac x=x in sp_notin_dset_pre)
apply assumption
done

lemma all_in_ex :"\<lbrakk>  \<forall> x\<in>A. P x;  A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists> x\<in> A. P x "
apply blast
done

lemma "\<forall>x. x\<in>A \<longrightarrow> P x \<Longrightarrow> \<forall> x\<in> A. P x " by auto
lemma " \<forall> x\<in> A. P x  \<Longrightarrow> \<forall>x. x\<in>A \<longrightarrow> P x" by auto

lemma  (in topological_space) nb_ex_onb:
 "\<lbrakk> U \<in> neighborhood_system x \<rbrakk> \<Longrightarrow> \<exists> U1. U1 \<in> open_neighborhood_system x"
apply (simp add:neighborhood_system_def open_neighborhood_system_def neighborhood_def open_neighborhood_def)
apply auto
done
lemma (in topological_space) open_nbs:
"\<lbrakk> open_set A; A \<in> neighborhood_system x\<rbrakk> \<Longrightarrow>   A \<in> open_neighborhood_system x"
apply (simp add:open_neighborhood_system_def 
                neighborhood_system_def 
                open_neighborhood_def 
                neighborhood_def 
                closed_set_def 
                open_set_def)
apply blast
done
lemma (in topological_space) open_nbs_o:
"\<lbrakk>  U \<in> open_neighborhood_system x \<rbrakk> \<Longrightarrow> open_set U"
apply (simp add:open_neighborhood_system_def
                neighborhood_def
                open_neighborhood_def
                open_set_def)
done

(*  \<lbrakk>A \<in> T; A \<subseteq> X; X - B \<in> T; B \<subseteq> X\<rbrakk> \<Longrightarrow> A - B \<in> T *)
lemma  subset_mui :"\<lbrakk> A \<subseteq> X  ; B \<subseteq> X\<rbrakk> \<Longrightarrow> (A - B) =  A \<inter> (X - B)"
apply blast
done

lemma (in topological_space) open_mui_closed_is_open:
"\<lbrakk> open_set A ; closed_set B\<rbrakk> \<Longrightarrow> open_set (A - B)"
apply (frule_tac A="A" in open_subset)
apply (simp add:open_set_def closed_set_def O4)
apply (subgoal_tac "A-B = A \<inter> (X - B)")
apply (simp)
apply blast
done

lemma (in topological_space) open_is_onb:
"\<lbrakk> open_set A; x \<in> A \<rbrakk> \<Longrightarrow>  A \<in> open_neighborhood_system x"
apply (simp add: open_neighborhood_system_def open_neighborhood_def open_set_def)
done

lemma (in topological_space) onbs_in:
"A \<in> open_neighborhood_system x \<Longrightarrow> x \<in> A"
apply (simp add:open_neighborhood_system_def open_neighborhood_def)  
done

lemma (in topological_space) obb_mui_closed_onb:
"\<lbrakk> U \<in> open_neighborhood_system x ; closed_set A;  x \<notin> A \<rbrakk> \<Longrightarrow> U - A \<in> open_neighborhood_system x"
apply(frule open_nbs_o)
apply (frule_tac B=A in open_mui_closed_is_open)
apply assumption
apply (subgoal_tac "x\<in> (U - A)")
apply (simp add: open_is_onb)
apply (simp add: onbs_in)
done

lemma (in topological_space)
 YangChungTauTheorem:
assumes a0:"A \<subseteq> X"
 and a1: " \<forall> x\<in> X. closed_set (derived_set {x})"
shows "derived_set(derived_set A) \<subseteq> derived_set A"
proof-
from a1 have s1:"\<And>x. x \<in> derived_set(derived_set A)\<Longrightarrow> x \<in> derived_set A"
 proof-
  fix x 
  assume a2:"x \<in> derived_set(derived_set A)"
  show "x \<in> derived_set A"
  proof-
    from a2 have s1:"derived_set A \<subseteq> X" by (simp add:derived_set_def cluster_point_def)
    from a2 have s2:"x\<in> X"  apply (simp add:derived_set_def cluster_point_def) done
    from a2 have s3:"\<forall>U\<in> neighborhood_system  x.  U \<inter> ((derived_set A) -{x}) \<noteq> {}"  
          by (simp add:derived_set_def cluster_point_def)
    from s3 have s4:"\<forall>U\<in> open_neighborhood_system  x.  U \<inter> ((derived_set A) -{x}) \<noteq> {}"  
      apply (drule_tac x="x" and P="\<lambda>UU.( \<lambda>xx. ( UU \<inter> ((derived_set A) -{xx}) \<noteq> {}))" in open_nbs_intro)
    apply assumption done
    have s5:"\<And> U. U\<in> neighborhood_system x \<Longrightarrow>  U \<inter> (A -{x})\<noteq> {}" 
       proof-
          fix U1
          assume a3:"U1\<in> neighborhood_system  x"
          show " U1 \<inter> (A -{x})\<noteq> {}"
    proof-
    from a3 have s6:"\<exists>U . U\<in> open_neighborhood_system  x" apply (auto simp:nb_ex_onb) done
    from s6  obtain U where s7:"U\<in> open_neighborhood_system  x" apply auto done
    from s7 s4 a3 have  s8:" U \<inter> ((derived_set A) -{x}) \<noteq> {}" by auto
    let ?V = "U - (derived_set {x})"
    from s2 have s9:"?V \<in> open_neighborhood_system x" 
             apply (rule_tac A ="(derived_set {x})" in obb_mui_closed_onb) 
             apply (simp add:s7) 
             apply (simp add:a1)    
             apply (simp add:sp_notin_dset) done
    from s4 s9 have s10:" ?V \<inter> ((derived_set A) -{x}) \<noteq> {}" by blast
    from s10 have s11: "\<exists>y. y\<in> ?V \<inter> ((derived_set A) -{x}) " by auto
    from s11 obtain y where s12: "y\<in> ?V" and s13:"y\<in> ((derived_set A) -{x})" by blast
    from s12 s13 have s14:"y\<noteq> x" by auto
    from s12 s13 s14 have s15:"y\<notin> (derived_set {x}) " by blast
    from s2 have s16:"{x}\<subseteq> X" by blast
    from s2 s3 s15 s16 have s17:"\<exists>W \<in> open_neighborhood_system x. W \<inter> ({x}-{y})= {}"  by auto
    from s17 s14 obtain W where s18:"W \<in> open_neighborhood_system x" and s19:" W \<inter> {x}= {}" by auto
    from s19 have s20:"x\<notin> W" by blast
    from s18 s9 have s21:"W \<inter> ?V  \<in> (open_neighborhood_system y)" by auto
    from s21 have s22:"W \<inter> ?V  \<in> (neighborhood_system y)" sorry
    from s13 s14 have s23:"y\<in> derived_set A" by auto
    from s23 have s24:"\<forall>K\<in> neighborhood_system  y.  K \<inter> (A -{y}) \<noteq> {}" 
         by (auto simp:derived_set_def cluster_point_def)
    from s22 s24 have s25:"(W \<inter> ?V ) \<inter> (A -{y}) \<noteq> {}" by blast
    from s25 have s26: "\<exists>t. t\<in> (W \<inter> ?V ) \<inter> (A -{y}) " by auto
    from s26 obtain t where  s27:" t\<in> (W \<inter> ?V ) \<inter> (A -{y})" by auto
    from s27 have s28:"t\<in> W" by auto
    from s27 s20 have s29:"t\<noteq> x" by auto
    from s29 s27 s20 have s30:"t\<in> U \<inter> (A -{x})" by auto
    from s30 have s31:"U\<inter> (A - {x})\<noteq> {}" by auto
    from s31 show ?thesis ..
qed
qed
    from s5 a0  s2 show ?thesis by (simp add:derived_set_def cluster_point_def)
qed
\<and>
qed
    show ?thesis by auto
qed


definition (in topological_space)
   base :: " 'a set set \<Rightarrow> bool"  where
  "base S == S \<subseteq> T  \<and> ( \<forall>x\<in>T. \<exists> F \<subseteq> S. \<Union>F = x )" 


(*
lemma (in topology) base_inter[intro,simp]:
   "\<lbrakk> base S ; U1 \<in> S; U2\<in> S ; x \<in> U1 \<inter> U2 \<rbrakk> \<longrightarrow> \<exists> U3\<in> S. ( (x\<in> U3) \<and> (U3 \<subseteq>  U1 \<inter> U2))"
*)
definition(in topological_space)
  neighborhood_base :: "'a set set \<Rightarrow> 'a \<Rightarrow> bool"  where
  "neighborhood_base NB x ==( NB \<subseteq> (neighborhood_system x )) \<and> 
      ( \<forall>U \<in> (neighborhood_system x). \<exists>V\<in> NB. ((x \<in> V) \<and> (V \<subseteq> U))) "


definition (in topological_space)
  interior :: "'a set => 'a set " where
  "interior A = Union {a. (A <= X & open_set a & A <= a)}"

definition (in topological_space)
  closure :: "'a set \<Rightarrow> 'a set " where
  "closure A = Inter {c. (A \<subseteq> X \<and> closed_set c  \<and> A \<subseteq>  c) }"

lemma (in topological_space) open_set_10: 
    "{a \<in> T. A \<subseteq> a} \<subseteq> T"
apply blast
done
lemma  (in topological_space) 
  "A \<subseteq> X \<Longrightarrow> open_set (interior A)"
apply (simp add:open_set_def)
apply (simp add:interior_def)
apply (simp add:open_set_def)
apply (rule O5)
apply (rule open_set_10 )
done

(*lemma (in topological_space) 
  "\<lbrakk>U \<subseteq> X ;U \<in> T; U \<subseteq> A\<rbrakk> \<Longrightarrow> U \<subseteq> \<Union>{a. A \<subseteq> X \<and> a \<in> T \<and> A \<subseteq> a}"
apply auto
done*)

lemma  (in topological_space) closure_is_closed:
       "[| open_set U ;  U <= B |] 
        ==>  U <= interior B"
apply (unfold interior_def)
apply (unfold open_set_def)
apply auto
done



lemma (in topological_space)
    "[| open_set U ; closed_set C |] ==> open_set (U -C)"
apply (simp add:open_set_def closed_set_def)
apply done
done

lemma (in topological_space)
    "[| open_set U ; closed_set C |] ==> closed_set (C -U)"
apply (simp add:open_set_def closed_set_def)
apply blast
done




end 
