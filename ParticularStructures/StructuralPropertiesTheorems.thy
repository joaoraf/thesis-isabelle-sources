subsection \<open>Permutability and Isomorphical Uniqueness\<close>

theory StructuralPropertiesTheorems
  imports IsomorphicalUniqueness Permutability CollapsibleParticulars
begin

context ufo_particular_theory
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>It turns out that the set of isomorphically unique particulars of a particular
  structure is identical to the set of non-permutable particulars, as shown in the 
  following theorem and lemmas:\<close>

lemma im_unique_particulars_are_non_permutable_particulars: 
    \<open>\<P>\<^sub>\<simeq>\<^sub>! \<subseteq> \<P>\<^sub>1\<^sub>!\<close>
proof (intro subsetI ballI ; clarsimp simp: isomorphically_unique_particulars_def)
  fix x \<phi> y
  assume as1: \<open>particular_struct_endomorphism \<Gamma> \<phi>\<close> \<open>x \<in> \<E>\<close>
      \<open>\<forall>\<phi>\<in>BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>. 
       \<forall>\<sigma>\<in>Morphs\<^bsub>\<Gamma>,MorphImg \<phi> \<Gamma>\<^esub>.
       \<forall>y\<in>\<E>. \<sigma> y = \<phi> x \<longleftrightarrow> y = x\<close>
      \<open>y \<in> \<E>\<close>  
  interpret I: particular_struct_endomorphism \<Gamma> \<phi> using as1(1) by blast
(*  interpret I2: particular_struct_bijection_1 \<Gamma> \<phi> using as1(1) by blast *)
  have A: \<open>\<sigma> y = \<phi> x \<longleftrightarrow> y = x\<close> if 
    \<open>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close> \<open>\<sigma> \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<phi> \<Gamma>\<^esub>\<close> \<open>y \<in> \<E>\<close> 
    for \<phi> \<sigma> y
    using that as1(3) by metis
  obtain \<theta> :: \<open>'p \<Rightarrow> ZF\<close> where \<open>inj \<theta>\<close>
    using injection_to_ZF_exist by blast
  define \<gamma> where \<open>\<gamma> x \<equiv> Opair (\<theta> x) undefined\<close> for x
  have \<gamma>_inj: \<open>inj_on \<gamma> \<P>\<close>
    using \<open>inj \<theta>\<close> by (simp add: Opair \<gamma>_def inj_on_def)
  define \<pi> where \<open>\<pi> \<equiv> restrict \<gamma> \<P>\<close>
  have \<pi>\<^sub>1: \<open>inj_on \<pi> \<P>\<close>
    apply (auto simp: \<pi>_def)
    using \<gamma>_inj inj_on_subset by blast
  have ex_inj: \<open>\<exists>f::ZF \<Rightarrow> ZF. inj f\<close> using inj_on_id by blast
  have \<pi>_ext: \<open>\<pi> \<in> extensional \<E>\<close>
    by (auto simp: \<pi>_def extensional_def)
  have \<pi>_img: \<open>undefined \<notin> \<pi> ` \<E>\<close>
    apply (auto simp: \<pi>_def \<gamma>_def)    
    by (metis Elem_Opair_exists notsym_Elem)    
  have pi_isomorph: \<open>\<pi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>\<close>
    by (intro inj_morph_img_BijMorphs \<pi>\<^sub>1 ex_inj \<pi>_ext \<pi>_img)
  have pi_sigma_morph: \<open>\<pi> \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<phi> \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<pi> \<Gamma>\<^esub>\<close>
    by (meson I.particular_struct_morphism_axioms bijections1_are_morphisms
        morphisms_are_closed_under_comp morphs_I pi_isomorph)
  have pi_x_pi_phi_x: \<open>\<pi> x = \<pi> (\<phi> x)\<close>
    using A[of \<open>\<pi>\<close> \<open>\<pi> \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<phi>\<close>, 
          OF pi_isomorph pi_sigma_morph \<open>x \<in> \<E>\<close>,simplified]
         compose_eq[OF \<open>x \<in> \<E>\<close>,of \<pi> \<phi>] 
    by simp    
  have I_ends[simp]: \<open>I.endurants = \<E>\<close> by simp
  then have \<open>\<phi> x \<in> \<E>\<close>
    using I.morphism_scope_particulars \<open>x \<in> \<E>\<close> by auto  

  have T: \<open>x = \<phi> x\<close>
    apply (rule \<pi>\<^sub>1[THEN inj_onD,OF _ \<open>x \<in> \<E>\<close> \<open>\<phi> x \<in> \<E>\<close>])
    by (intro \<open>\<pi> x = \<pi> (\<phi> x)\<close>)    
  show \<open>\<phi> y = x \<longleftrightarrow> y = x\<close>
    using T 
    apply (intro iffI ; simp?)  
    using A[where y=y and \<phi> = \<pi> and \<sigma> = \<open>\<pi> \<circ>\<^bsub>\<P>\<^esub> \<phi>\<close>
         ,OF pi_isomorph _ \<open>y \<in> \<E>\<close>, OF pi_sigma_morph[simplified I_ends]
         , simplified compose_eq[OF \<open>y \<in> \<E>\<close>] pi_x_pi_phi_x
         ,simplified
         ]
    by metis      
qed

lemma non_permutable_particulars_are_im_unique_particulars: 
  \<open>\<P>\<^sub>1\<^sub>! \<subseteq> \<P>\<^sub>\<simeq>\<^sub>!\<close>
proof (intro subsetI ballI ; clarsimp simp: isomorphically_unique_particulars_def)
  fix x y :: \<open>'p\<close> and \<phi> \<sigma> :: \<open>'p \<Rightarrow> 'p\<^sub>1\<close> and f :: \<open>'p\<^sub>1 \<Rightarrow> ZF\<close>
  assume as: 
      \<open>particular_struct_morphism \<Gamma> (MorphImg \<phi> \<Gamma>) \<sigma>\<close>       
      \<open>\<forall>\<phi>\<in>EndoMorphs\<^bsub>\<Gamma>\<^esub>. \<forall>y\<in>\<E>. \<phi> y = x \<longleftrightarrow> y = x\<close> 
      \<open>inj_on \<phi> \<E>\<close> 
      \<open>inj f\<close>     
      \<open>x \<in> \<E>\<close>
      \<open>y \<in> \<E>\<close>
      \<open>\<phi> \<in> extensional \<E>\<close>
      \<open>undefined \<notin> \<phi> ` \<E>\<close>
  have A: \<open>\<phi> y = x \<longleftrightarrow> y = x\<close> if \<open>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close> \<open>y \<in> \<E>\<close> for \<phi> y using as(2) that by blast  
  interpret I1: particular_struct_morphism \<open>\<Gamma>\<close> \<open>MorphImg \<phi> \<Gamma>\<close> \<open>\<sigma>\<close> using as(1) by simp
  interpret I: particular_struct_bijection_1 \<open>\<Gamma>\<close> \<open>\<phi>\<close>
    using as(3,4,7,8) inj_morph_img_isomorphism[of \<open>\<phi>\<close>] by blast
  interpret Inv: particular_struct_bijection_1 \<open>MorphImg \<phi> \<Gamma>\<close> \<open>I.inv_morph\<close>    
    using particular_struct_bijection_iff_particular_struct_bijection_1 by blast

  have B: \<open>particular_struct_morphism \<Gamma> \<Gamma> (I.inv_morph \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<sigma>)\<close>    
    apply (intro particular_struct_morphism_comp[of _ \<open>MorphImg \<phi> \<Gamma>\<close>])
    subgoal using I1.particular_struct_morphism_axioms by blast
    subgoal
      using particular_struct_bijection.axioms(1) 
            particular_struct_injection.axioms(1) 
            I.inv_is_bijective_morphism
      by metis
    done
  then interpret inv_sigma: particular_struct_morphism \<Gamma> \<Gamma> \<open>Inv \<E> \<phi> \<circ>\<^bsub>\<E>\<^esub> \<sigma>\<close> 
    by simp

  have C: \<open>Inv \<E> \<phi> \<circ>\<^bsub>\<E>\<^esub> \<sigma> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close>
    apply (simp)
    by (intro_locales) 

  have D: \<open>Inv \<E> \<phi> (\<sigma> x) = x\<close> 
    using A[OF C \<open>x \<in> \<E>\<close>]  
    by (auto simp add: compose_eq \<open>x \<in> \<E>\<close>)
  have E: \<open>Inv \<E> \<phi> (\<phi> x) = x\<close>
    by (intro Inv_f_eq \<open>x \<in> \<E>\<close> \<open>inj_on \<phi> \<E>\<close>)      
  have endo: \<open>particular_struct_endomorphism \<Gamma> (Inv \<E> \<phi> \<circ>\<^bsub>\<E>\<^esub> \<sigma>)\<close>
    by (intro_locales)
  have F: \<open>Inv \<E> \<phi> (\<sigma> x) = Inv \<E> \<phi> (\<phi> x)\<close> using D E by simp
  show \<open>\<sigma> y = \<phi> x \<longleftrightarrow> y = x\<close>
    apply (intro iffI ; simp?)
    subgoal
      supply R = A[where y=y and \<phi> = \<open>Inv \<E> \<phi> \<circ>\<^bsub>\<E>\<^esub> \<sigma>\<close>,OF C \<open>y \<in> \<E>\<close>,THEN iffD1
                , simplified compose_eq[OF \<open>y \<in> \<E>\<close>]] D[simplified]
      by (rule A[THEN iffD1, of \<open>Inv \<E> \<phi> \<circ>\<^bsub>\<E>\<^esub> \<sigma>\<close>] ; (simp add: as compose_eq endo)?) 
    subgoal      
      apply (rule F inj_onD[OF Inv.morph_is_injective[simplified],simplified,OF F])
      subgoal using \<open>x \<in> \<E>\<close> by (simp add: I1.morph_preserves_particulars)
      using \<open>x \<in> \<E>\<close> by (simp add: I.morph_preserves_particulars)
    done 
qed

theorem non_permutable_particulars_are_the_unique_particulars: 
    \<open>\<P>\<^sub>1\<^sub>! = \<P>\<^sub>\<simeq>\<^sub>!\<close>
  using im_unique_particulars_are_non_permutable_particulars
     non_permutable_particulars_are_im_unique_particulars by simp    


text \<^marker>\<open>tag bodyonly\<close> \<open>
  The set of non-permutable particulars is a subset of the set of
  non-collapsible particulars, although the converse does not
  hold, in general:
\<close>

theorem  non_permutables_are_non_collapsible: \<open>\<P>\<^sub>1\<^sub>! \<subseteq> \<P>\<^sub>n\<^sub>c\<close> 
proof (intro subsetI ; elim non_permutables_E ; 
        intro nonCollapsibleParticularsI notI ;
        (elim collapsibleE)? ; assumption?
        ; rename_tac x\<^sub>1 \<phi> x\<^sub>2)
  fix x\<^sub>1 x\<^sub>2 \<phi>
  assume A: \<open>x\<^sub>1 \<in> \<E>\<close> \<open>x\<^sub>2 \<in> \<E>\<close> \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> \<open>\<phi> x\<^sub>1 = \<phi> x\<^sub>2\<close>            
    and B: \<open>non_permutable x\<^sub>1\<close> \<open>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close>   
  note A(1,2)[simp,intro!]
  note A1[simp] = A(3)[simplified A(4)] A(4)
  interpret phi: particular_struct_endomorphism \<Gamma> \<phi> using B(2) by simp
  note C1 = B(1)[THEN non_permutable_E,OF B(2) \<open>x\<^sub>2 \<in> \<E>\<close>] and
       C2 = B(1)[THEN non_permutable_E,OF B(2) \<open>x\<^sub>1 \<in> \<E>\<close>]
  have D[simp]: \<open>\<phi> x\<^sub>1 = x\<^sub>1\<close> using C2 by simp     
  show False    
    using A1(1) A1(2) C1 D by presburger
qed


end

end