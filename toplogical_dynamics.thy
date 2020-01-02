theory topological_dynamics imports continuous   begin

definition (in topological_space )
  covering ::"'a set set \<Rightarrow> bool"where
 "covering C \<longleftrightarrow> (\<Union>C = X \<and> C \<subseteq> Pow X ) "

definition (in topological_space)
  open_covering ::"'a set set \<Rightarrow> bool" where
  "open_covering C \<longleftrightarrow> (covering C \<and>  (\<forall>c\<in>C. (open_set c)))"

definition (in topological_space)
  compact where
  "compact \<longleftrightarrow> ( \<forall>C. (open_covering C)\<longrightarrow>  (\<exists>A. ( A \<subseteq> C   \<and>  \<Union>A = X \<and>  finite A )) )"
  
thm  topological_space.compact_def


locale Group =
  fixes G
  fixes f 
  fixes e
  fixes f_inv
  assumes G1: "e\<in> G"
    and   G2: "\<forall>x\<in>G. f(x,e) = x "  
    and   G3: "\<forall>x\<in>G. f(e,x) = x"
    and   G4: "f: G \<times> G \<rightarrow> G"
    and   G5: "f_inv: G \<rightarrow> G"
    and   G6: "\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. f(f(x,y),z)=f(x,f(y,z))"
    and   G7: "\<forall>x\<in>G. f(x,f_inv(x))=e"
    and   G8: "\<forall>x\<in>G. f(f_inv(x),x)=e"
thm Group_def
(*  this is Tx is top
definition product_topology_base where
   "product_topology_base Tx Ty \<equiv>{u. \<forall>x\<in>Tx. \<forall>y\<in>Ty. ( (u=(x \<times> y)) \<and>  (topological_space (\<Union>Tx) Tx) \<and>  (topological_space (\<Union>Ty) Ty))  

}"*)

definition product_topology_base where
   "product_topology_base Tx Ty \<equiv>{b. \<forall>x\<in>Tx. \<forall>y\<in>Ty.  (b=(x \<times> y)) }"


definition
  "product_topology Tx Ty  \<equiv>  {t.  \<forall>p \<in> Pow(product_topology_base Tx Ty ). t=\<Union>p}"


locale topological_group = topological_space +
  fixes f
  fixes e
  fixes f_inv
  assumes tg1:"Group X f e f_inv"
   and    tg2:"continuous f  (X\<times>X) (product_topology T T) X T"
   and    tg3:"continuous f_inv X T X T"
thm topological_group_def

thm topological_group_axioms_def


locale topological_transformation_group = topological_group +
  fixes M
  fixes Tm
  fixes mappi ("\<phi>  _" 89)
  assumes istop :"topological_space M Tm"
  assumes map1 : "mappi : (X  \<times>  M \<rightarrow>  M)"
  assumes ident : "\<forall>x \<in> M.  \<phi> (x, e) = x"
  assumes Homom:   "\<forall>x\<in>M. \<forall>g1\<in>X. \<forall>g2\<in>X. \<phi>(g1,\<phi>(g2,x) ) = \<phi>(f(g1,g2),x)"
  assumes Conti:   "continuous f  (X\<times>M) (product_topology T Tm ) M Tm" 

locale hausdorff_space = topological_space +
      assumes t1 : "!! x1 x2. [|x1: X; x2: X; x1 ~= x2 |]
                    ==> EX U V. (neighborhood U x1)  &
                            (neighborhood V x2)  &
                             x2 ~: U & x1 ~: V "
thm hausdorff_space_def
thm topological_space.compact_def

locale topological_dynamic_system =
    topological_transformation_group +
  assumes iscompact :"topological_space.compact M Tm"
  assumes map1 : "hausdorff_space M Tm"

thm topological_dynamic_system_def

definition (in topological_transformation_group )
  invariant_set where
  "invariant_set A \<longleftrightarrow> (A \<subseteq> M \<and> (\<forall>g \<in> X.  {x. \<exists>a\<in>A. x = \<phi>(g,a)} \<subseteq> A)) " 



lemma forall_conjI:"\<lbrakk> (\<forall>x\<in>X. (P x)); (\<forall>x\<in>X. (Q x))\<rbrakk> \<Longrightarrow> \<forall>x\<in>X. (P x) \<and> (Q x)"
apply blast
done

lemma "\<lbrakk>\<forall>x\<in>X. (P x) \<and> (Q x)\<rbrakk> \<Longrightarrow> (\<forall>x\<in>X. (P x)) \<and> (\<forall>x\<in>X. (Q x))"
apply blast
done 

lemma  "\<lbrakk>A \<subseteq> M; B \<subseteq> M\<rbrakk> \<Longrightarrow> A \<inter> B \<subseteq> M"
apply blast
done 
lemma (in topological_transformation_group)
int_is_inv:
"\<lbrakk> invariant_set A; invariant_set B \<rbrakk> \<Longrightarrow> invariant_set (A \<inter> B)"
apply (simp add :invariant_set_def)
apply (rule conjI)
apply (drule_tac  conjunct1)
apply (drule_tac  conjunct1)
apply (blast 1)
apply (drule_tac conjunct2)
apply (drule_tac  conjunct2)
apply (rule forall_conjI)
apply blast
apply (rotate_tac 1)
apply blast
done
(*
lemma  (in topological_transformation_group) closure_is_invariant:
  "invariant_set A ==> invariant_set (closure A) "
apply (simp add :closure_def invariant_set_def)
apply (rule conjI)
apply (drule_tac conjunct1)
apply (drule_tac conjunct1)
apply (simp add:Lattices.lower_semilattice_class.le_infI1)
apply (drule_tac conjunct2)
apply (drule_tac conjunct2)
apply (rule forall_conjI)
apply blast
apply (rotate_tac 1)
apply blast
*)

lemma (in topological_transformation_group)
int_is_inv1:
assumes a1: "invariant_set A"
 and  a2:" invariant_set B"
shows "invariant_set (A\<inter>B)"
proof-
 from a1 have s1:"A \<subseteq> M" by (simp add:invariant_set_def)
 from a2 have s2:"B \<subseteq> M" by (simp add:invariant_set_def)
 from s1 s2 have s3: "A \<inter> B \<subseteq> M" by blast
 from a1 have s4:"\<forall>g \<in> X.  {x. \<exists> a\<in>A. x = \<phi>(g,a)} \<subseteq> A" by (simp add:invariant_set_def)
 from a2 have s5:"\<forall>g \<in> X.  {x. \<exists> a\<in>B. x = \<phi>(g,a)} \<subseteq> B" by (simp add:invariant_set_def)
 from s4 s5 have s6:"\<forall>g \<in> X. {x. \<exists> a\<in>A. x = \<phi>(g,a)} \<subseteq> A  \<and>  {x. \<exists>a\<in>B. x = \<phi>(g,a)} \<subseteq> B" by (simp) 
 from s4 have s7:"\<And> g. g \<in> X \<Longrightarrow>  {x. \<exists>a\<in>A \<inter> B. x = \<phi>(g,a)} \<subseteq>  A"  apply blast done 
 from s5 have s8:"\<And> g. g \<in> X \<Longrightarrow>  {x. \<exists>a\<in>A \<inter> B. x = \<phi>(g,a)} \<subseteq>  B"  apply blast done 
 from s7 s8 have s9:"\<And> g. g \<in> X \<Longrightarrow>  {x. \<exists>a\<in>A \<inter> B. x = \<phi>(g,a)} \<subseteq>  A \<inter> B" apply auto done
 from s1 s2 s9 show ?thesis apply (simp add:invariant_set_def)  apply blast done
qed

lemma dddd:"y \<in> {x. \<exists> a\<in> A\<union> B . x =P a} \<Longrightarrow>  y \<in> {x. \<exists> a\<in> A. x =P a} \<or> y \<in> {x. \<exists> a\<in> B. x =P a}"
apply blast
done

lemma eeee:"{x. \<exists> a\<in> A\<union> B . x =P a}\<subseteq>  {x. \<exists> a\<in> A. x =P a} \<union> {x. \<exists> a\<in> B. x =P a}"
apply auto
done


lemma (in topological_transformation_group)
union_is_inv:
assumes a1: "invariant_set A"
 and  a2:" invariant_set B"
shows "invariant_set (A \<union> B)"
proof-
 from a1 have s1:"A \<subseteq> M" by (simp add:invariant_set_def)
 from a2 have s2:"B \<subseteq> M" by (simp add:invariant_set_def)
 from s1 s2 have s3: "A \<union>  B \<subseteq> M" by blast
 from a1 have s4:"\<And>g. g \<in> X \<Longrightarrow>   {x. \<exists> a\<in>A. x = \<phi>(g,a)} \<subseteq> A" by (simp add:invariant_set_def)
 from a2 have s5:"\<And>g. g \<in> X \<Longrightarrow> {x. \<exists> a\<in>B. x = \<phi>(g,a)} \<subseteq> B" by (simp add:invariant_set_def)
 from s4 s5 have s6:"\<And>g. g \<in> X \<Longrightarrow>  {x. \<exists> a\<in>A. x = \<phi>(g,a)} \<subseteq> A  \<and>  {x. \<exists>a\<in>B. x = \<phi>(g,a)} \<subseteq> B" by (simp)
 from s6 have s7: "\<And>g. g \<in> X \<Longrightarrow>  {x. \<exists> a\<in>A \<union> B. x = \<phi>(g,a)} \<subseteq>  {x. \<exists> a\<in>A. x = \<phi>(g,a)} \<union> {x. \<exists> a\<in>B. x = \<phi>(g,a)}" 
 by blast
 from s7 s6 have s8:"\<And> g. g \<in> X \<Longrightarrow>  {x. \<exists>a\<in>A \<union>  B. x = \<phi>(g,a)} \<subseteq>  A \<union> B" 
   proof- 
     fix g assume a8_1: "g \<in> X"
     show "{x. \<exists>a\<in>A \<union>  B. x = \<phi>(g,a)} \<subseteq>  A \<union> B"
     proof- 
        from a8_1  s7 have s8_1: "{x. \<exists> a\<in>A \<union> B. x = \<phi>(g,a)} \<subseteq>  {x. \<exists> a\<in>A. x = \<phi>(g,a)} \<union> {x. \<exists> a\<in>B. x = \<phi>(g,a)}" apply simp done
        from a8_1 s4 have s8_2:" {x. \<exists> a\<in>A. x = \<phi>(g,a)} \<subseteq> A" by simp
        from a8_1 s5 have s8_3:" {x. \<exists> a\<in>B. x = \<phi>(g,a)} \<subseteq> B" by simp
        from s8_1 s8_2 s8_3 show ?thesis by blast
 qed
qed        
 from s3 s8 show ?thesis apply (simp add:invariant_set_def)  done 
qed



(*

(*
lemma  (in topological_transformation_group) closure_is_invariant:
  "invariant_set A ==> invariant_set (closure A) "
apply (simp add :closure_def invariant_set_def)
apply (rule conjI)
apply (drule_tac conjunct1)
apply (drule_tac conjunct1)
apply (simp add:Lattices.lower_semilattice_class.le_infI1)
apply (drule_tac conjunct2)
apply (drule_tac conjunct2)
apply (rule forall_conjI)
apply blast
apply (rotate_tac 1)
apply blast
*)
*)
(*
lemma "\<lbrakk> A\<Longrightarrow>B \<rbrakk> \<Longrightarrow>  A\<longrightarrow> B" impI *)

thm topological_transformation_group_def
lemma (in topological_transformation_group)
 " \<lbrakk>g \<in> X; x\<in> M \<rbrakk> \<Longrightarrow> \<phi> (g, x) \<in> M"
apply (insert map1)
apply blast
done

lemma (in topological_transformation_group)
"\<lbrakk> g\<in>X; h= (\<lambda>x. \<phi>(g,x)) \<rbrakk> \<Longrightarrow> (h: M\<rightarrow>M)"
apply (insert map1)
apply blast
done

definition orbit where
  "orbit x G = {g}"

definition product1 where
  "product1 A B \<equiv> (A \<times> B) "



definition product2 where
  "product2 A B \<equiv> {(product1 a b). ( a \<subseteq> A  \<and> b \<subseteq> B)} "


(*lemma "\<lbrakk> A\<subseteq> B; C \<subseteq> D \<rbrakk> \<Longrightarrow> (A \<times> C) \<subseteq> (B \<times> D)"
*)


thm times_def

definition ProductTopology where
  "ProductTopology T S \<equiv>  {\<Union>W. W \<in> Pow(ProductCollection T S)}"

definition  product_topology  where
 "product X Y ="
lemma "\<lbrakk> topological_space X Tx;topological_space Y Ty \<rbrakk> \<Longrightarrow> "

locale 
(*
  defines prodtop_def [simp]: "$\tau \equiv$ ProductTopology(T,T)"
  fixes f
  assumes isgroup: "IsAgroup(G,f)"
  assumes isconti: "IsContinuous($\tau$,T,f)"
  assumes invisconti: "IsContinuous(T,T,GroupInv(G,f))"*)

(*  defines G_def [simp]: "G $\equiv \bigcup$ T"
  fixes prodtop ("$\tau$")
  defines prodtop_def [simp]: "$\tau \equiv$ ProductTopology(T,T)"
  fixes f
  assumes isgroup: "IsAgroup(G,f)"
  assumes isconti: "IsContinuous($\tau$,T,f)"
  assumes invisconti: "IsContinuous(T,T,GroupInv(G,f))"*)

lemma "\<lbrakk> topological_space X T ;
         Y = (X \<times> X); 
         Ty = (ProductTopology T T) \<rbrakk> \<Longrightarrow> topological_space Y Ty "
apply (si)

definition product_topology1 where
   "product_topology1 X Tx  Y Ty \<equiv> \<Union>{u. \<exists>x\<in>Tx. \<exists>y\<in>Ty. ( (u=(x \<times> y)) \<and>  
                (topological_space X  Tx) \<and> 
                 (topological_space Y Ty))  }"*)
(*
lemma "\<lbrakk> topological_space X  (T::'a set set) ;Y = (X \<times> X) \<rbrakk> \<Longrightarrow> (product_topology1 T T) \<subseteq> Pow Y  "

lemma "\<lbrakk> topological_space X  T ;
          Y = (X \<times> X) ; 
          Ty = Pow Y
       \<rbrakk> \<Longrightarrow>  Y \<in> Ty"

lemma "\<lbrakk> topological_space X  T ;
     orbit     Y = (X \<times> X) ; 
          Ty = (product_topology1 X T X T ) 
       \<rbrakk> \<Longrightarrow> topological_space Y Ty "
apply (simp add:product_topology_def topological_space_def)


end