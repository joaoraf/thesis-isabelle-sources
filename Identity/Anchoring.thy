section \<open>Identity Through Identity Anchors\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In this section, we describe another approach for characterizing
  the identity of a particular in a particular structure. Though we
  prove that this approach is logically equivalent to the characterizations
  based on identifiability, non-permutability or isomorphical uniqueness,
  it nevertheless is able to better highlight the context that characterizes
  the identity of a particular. 
\<close>
text_raw\<open>\par\<close>
text_raw \<open>\subsection[Anchoring]{Anchoring\isalabel{subsec:anchoring}}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The value of an ontology, or conceptual model, lies in the information it
  carries about the concepts and assumptions that characterize a domain.
  In the context of Information Systems development, one of the most important 
  users of a conceptual model is the database designer, and some
  of the elements the DB designer expects to find in the conceptual model
  are the identity conditions of the elements in the domain.

  The definitions provided so far for the identity of particulars were 
  (1) by identifiability, (2) by isomorphical uniqueness, and (3) by
  non-permutability. The first one has the disadvantage of requiring
  the existence of a predicate (and of a formal language) at a
  fundamental level in the foundational ontology, even though such
  predicate would be useful for the purposes of the DB designer. The
  other two, though not requiring the existence of elements that are
  not in the particular structure, simply provides us a yes or no 
  answer to whether a particular has identity.

  Here we introduce the notion of an \emph{identity anchor} as a
  structure that represents the \emph{identity neighborhood} of a
  particular in a particular structure, i.e., the elements of the
  structure that play a role in the identification of the particular.
  Note that we are not referring to the identity condition itself,
  which would be a predicate, but to the elements of the structure 
  that would participate in some identity predicate.
\<close>
text_raw\<open>\par\<close>
theory Anchoring
  imports "../ParticularStructures/SubStructures"
begin

context ufo_particular_theory_sig
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
   Given a particular structure \<open>\<Gamma>\<close> and a particular \<open>x\<close> of \<open>\<Gamma>\<close>, and
   given another particular structure \<open>\<Gamma>\<^sub>x\<close>, a particular \<open>y\<close> of \<open>\<Gamma>\<^sub>x\<close>,
   and a morphism \<open>\<phi>\<close> from \<open>\<Gamma>\<^sub>x\<close> to \<open>\<Gamma>\<close>, we say that \<open>(\<Gamma>\<^sub>x,y,\<phi>)\<close> anchors
   \<open>x\<close> in \<open>\<Gamma>\<close>, written as \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close>, or that \<open>(\<Gamma>\<^sub>x,y,\<phi>)\<close> is an
   anchor for \<open>x\<close> (in \<open>\<Gamma>\<close>),  if and only if, for every
   morphism \<open>\<sigma>\<close> from \<open>\<Gamma>\<^sub>x\<close> to \<open>\<Gamma>\<close>, \<open>\<sigma> y\<close> is always \<open>x\<close>.

   In other words, there are sufficient elements in \<open>\<Gamma>\<^sub>x\<close> to make it
   so that \<open>y\<close> (in \<open>\<Gamma>\<^sub>x\<close>) cannot be seen as anything but \<open>x\<close> in \<open>\<Gamma>\<close>.
   Formally, we have:
\<close>
text_raw\<open>\par\<close>
definition anchors :: 
     \<open>   'p\<^sub>2 
       \<Rightarrow> ('p\<^sub>2,'q) particular_struct 
       \<Rightarrow> ('p\<^sub>2 \<Rightarrow> 'p) 
       \<Rightarrow> 'p 
       \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_,_\<rightarrow>\<^sub>1 _\<close> [74,1,1,74] 75) where
  \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x \<equiv> 
       x \<in> \<P> \<and> \<Gamma>\<^sub>x \<lless>\<^bsub>\<phi>\<^esub> \<Gamma> \<and> y \<in> particulars \<Gamma>\<^sub>x 
     \<and> (\<forall>\<sigma> \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub>. \<forall>z \<in> particulars \<Gamma>\<^sub>x. \<sigma> z = x \<longleftrightarrow> z = y)\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
   Note that, since \<open>x\<close> is invariant with respect to the morphisms from 
   \<open>\<Gamma>\<^sub>x\<close> to \<open>\<Gamma>\<close>, the choice of the morphism \<open>\<phi>\<close> doesn't matter. Thus,
   we can just say that \<open>(\<Gamma>\<^sub>x,y)\<close> anchors \<open>x\<close>, or simply that \<open>\<Gamma>\<^sub>x\<close> is
   an anchor for \<open>x\<close>.
   Note that from a particular structure with a single particular, \<open>y\<close>, we
   can always have a morphism to \<open>\<Gamma>\<close> that maps \<open>y\<close> to \<open>x\<close>. However, this
   configuration would only work as anchor for \<open>x\<close> if \<open>x\<close> is the only
   substantial in \<open>\<Gamma>\<close>. Otherwise, there would be morphisms from the
   single-particular structure to any substantial in \<open>\<Gamma>\<close>. Thus, it always
   possible to remove enough elements from an anchor in such a way that it
   stops being an anchor. Conversely, if \<open>\<Gamma>'\<close> is an anchor for \<open>x\<close>, then
   the addition of new elements to \<open>\<Gamma>'\<close>, while maintaing the existence of
   at least one morphism to \<open>\<Gamma>\<close>, will not remove its status as an anchor
   for \<open>x\<close>.   
\<close>
text_raw\<open>\par\<close>
lemma \<^marker>\<open>tag (proof) aponly\<close> \<^marker>\<open>tag (proof) aponly\<close> anchorsI[intro!]:
  assumes 
    \<open>x \<in> \<P>\<close> \<open>\<Gamma>\<^sub>x \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<close> \<open>y \<in> particulars \<Gamma>\<^sub>x\<close>
    \<open>\<And>\<phi> z. \<lbrakk> z \<in> particulars \<Gamma>\<^sub>x ; \<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub> \<rbrakk> 
        \<Longrightarrow> \<phi> z = x \<longleftrightarrow> z = y\<close>
  shows \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close>  
  apply (simp add: anchors_def assms(1,2,3) 
              del: morphs_iff injectives_iff)
  apply (intro ballI)            
  using assms by metis

lemma  \<^marker>\<open>tag (proof) aponly\<close> anchorsE[elim!]:
  assumes \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close>
  obtains     
    \<open>x \<in> \<P>\<close> \<open>\<Gamma>\<^sub>x \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<close> \<open>y \<in> particulars \<Gamma>\<^sub>x\<close>
    \<open>\<And>\<phi> z. \<lbrakk> z \<in> particulars \<Gamma>\<^sub>x ; \<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub> \<rbrakk> 
        \<Longrightarrow> \<phi> z = x \<longleftrightarrow> z = y\<close>
  using assms by (simp add: anchors_def)

definition anchored_particulars :: \<open>'p set\<close> (\<open>\<P>\<^sub>\<down>\<close>) where
  \<open>\<P>\<^sub>\<down> \<equiv> { x | x (y :: ZF) \<Gamma>\<^sub>x \<phi> . y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x }\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> anchored_particulars_I[intro]:
  fixes y :: ZF and \<Gamma>\<^sub>x and x
  assumes \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close>
  shows \<open>x \<in> \<P>\<^sub>\<down>\<close>
  using assms 
  by (simp add: anchored_particulars_def ; metis)

lemma \<^marker>\<open>tag (proof) aponly\<close> anchored_particulars_E[elim!]:
  assumes \<open>x \<in> \<P>\<^sub>\<down>\<close>
  obtains y :: ZF and \<Gamma>\<^sub>x \<phi> where \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close>
  using assms 
  by (simp add: anchored_particulars_def ; metis)


lemma \<^marker>\<open>tag (proof) aponly\<close> anchored_particulars_I1[intro!]:
  fixes y :: \<open>'p\<^sub>1\<close>
  assumes \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<^sub>x\<rightarrow>\<^sub>1 x\<close>
  shows \<open>x \<in> \<P>\<^sub>\<down>\<close>
proof -
  obtain A: \<open>x \<in> \<P>\<close>  \<open>\<Gamma>\<^sub>x \<lless>\<^bsub>\<phi>\<^sub>x\<^esub> \<Gamma>\<close> \<open>y \<in> particulars \<Gamma>\<^sub>x\<close>
     and B: \<open>\<And>\<phi> z. \<lbrakk> z \<in> particulars \<Gamma>\<^sub>x 
                   ; \<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> \<phi> z = x \<longleftrightarrow> z = y\<close>
    using assms by blast
  interpret I: particular_struct_injection \<open>\<Gamma>\<^sub>x\<close> \<open>\<Gamma>\<close> \<open>\<phi>\<^sub>x\<close> 
    using A(2) by simp
  obtain \<sigma> :: \<open>'p\<^sub>1 \<Rightarrow> ZF\<close> where \<open>inj \<sigma>\<close> 
    using I.src.injection_to_ZF_exist by blast
  interpret I2: particular_struct_bijection_1 \<open>\<Gamma>\<^sub>x\<close> \<sigma> 
    using I.src.inj_morph_img_isomorphism[of \<sigma>]    
    by (metis I.src.\<Gamma>_simps UNIV_I \<open>inj \<sigma>\<close> inj_on_id inj_on_subset 
              particular_struct_eqI subsetI)
  have C: \<open>I2.tgt.\<Gamma> = MorphImg \<sigma> \<Gamma>\<^sub>x\<close> 
    using I2.tgt.\<Gamma>_simps by blast

  interpret I3: particular_struct_bijection_1 \<open>MorphImg \<sigma> \<Gamma>\<^sub>x\<close> \<open>inv \<sigma>\<close>
    apply (intro I2.tgt.inj_morph_img_isomorphism[simplified C])
    subgoal 
      by (metis I2.inv_morph_morph UNIV_I image_eqI 
                inj_on_inv_into subsetI)
    using I.src.injection_to_ZF_exist by blast

  have D[simp]: \<open>inv \<sigma> ` \<sigma> ` X = X\<close> for X
    using \<open>inj \<sigma>\<close> by (auto simp: image_def)

  have E[simp]: \<open>inv \<sigma> (\<sigma> x) = x\<close> for x
    using \<open>inj \<sigma>\<close> by (auto simp: image_def)
    
  have F[simp]: \<open>MorphImg (inv \<sigma>) (MorphImg \<sigma> \<Gamma>\<^sub>x) = \<Gamma>\<^sub>x\<close>
    apply (intro particular_struct_eqI ext 
          ; auto simp add: particular_struct_morphism_image_simps)
    subgoal using D by blast
    subgoal by force
    by (metis UNIV_I \<open>inj \<sigma>\<close> inv_into_f_f)
          
  interpret I4: particular_struct_injection \<open>MorphImg \<sigma> \<Gamma>\<^sub>x\<close> \<Gamma> \<open>\<phi>\<^sub>x \<circ> inv \<sigma>\<close>
    apply (intro particular_struct_injection_comp[of _ \<open>\<Gamma>\<^sub>x\<close>])
    using I3.particular_struct_injection_axioms[simplified]
          I.particular_struct_injection_axioms 
    by simp+

  have G: \<open>\<phi>\<^sub>x \<circ> inv \<sigma> \<in> InjMorphs\<^bsub>MorphImg \<sigma> \<Gamma>\<^sub>x,\<Gamma>\<^esub>\<close>
    using I4.particular_struct_injection_axioms by blast
  then have H: \<open>MorphImg \<sigma> \<Gamma>\<^sub>x \<lless>\<^bsub>\<phi>\<^sub>x \<circ> inv \<sigma>\<^esub> \<Gamma>\<close> by blast

  have J[simp]: \<open>(\<phi> z = x) = (z = \<sigma> y)\<close>
    if as: \<open>z \<in> I3.src.endurants\<close> 
           \<open>particular_struct_morphism (MorphImg \<sigma> \<Gamma>\<^sub>x) \<Gamma> \<phi>\<close> for z \<phi>
  proof -
    interpret I5: particular_struct_morphism \<open>MorphImg \<sigma> \<Gamma>\<^sub>x\<close> \<Gamma> \<phi> 
      using as by simp
    have AA: \<open>\<phi> \<circ> \<sigma> \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub>\<close>
      apply (intro morphs_I 
                particular_struct_morphism_comp[of _ \<open>MorphImg \<sigma> \<Gamma>\<^sub>x\<close>] as)      
      by (simp add: I2.particular_struct_morphism_axioms)
    have BB: \<open>inv \<sigma> z \<in> I.src.endurants\<close>      
      by (metis F I3.I_img_eq_tgt_I I3.morph_image_def image_eqI as(1))
    have CC:\<open>\<sigma> (inv \<sigma> z) = z\<close> using as(1) 
      by (meson BB E I2.morph_preserves_particulars 
                I3.morph_is_injective inj_onD)
    have DD: \<open>(\<phi> z = x) = (inv \<sigma> z = y)\<close>
      using B[OF BB AA] CC 
      by (simp ; metis)
    show ?thesis
      apply (simp add: DD)      
      using CC by auto      
  qed
  have K: \<open>\<sigma> y \<midarrow>MorphImg \<sigma> \<Gamma>\<^sub>x,\<phi>\<^sub>x \<circ> inv \<sigma>\<rightarrow>\<^sub>1 x\<close>
    apply (intro anchorsI I4.particular_struct_injection_axioms H A)
    using A(3) by auto
  show ?thesis 
    by (intro anchored_particulars_I[OF K])
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> anchor_to_zf_I:
  fixes y :: 'a
  assumes \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close>
  shows \<open>\<exists>(y\<^sub>1 :: ZF) \<Gamma>\<^sub>1 \<sigma>. y\<^sub>1 \<midarrow>\<Gamma>\<^sub>1,\<sigma>\<rightarrow>\<^sub>1 x \<and> \<Gamma>\<^sub>1 \<in> IsoModels\<^bsub>\<Gamma>\<^sub>x,TYPE(ZF)\<^esub>\<close>
proof -
  obtain A: \<open>x \<in> \<P>\<close> \<open>y \<in> particulars \<Gamma>\<^sub>x\<close> \<open>\<Gamma>\<^sub>x \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<close> 
            \<open>\<And>\<sigma> z. \<lbrakk> z \<in> particulars \<Gamma>\<^sub>x ; \<sigma> \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub> \<rbrakk> 
                \<Longrightarrow> \<sigma> z = x \<longleftrightarrow> z = y\<close>
    using anchorsE[OF assms] by metis
  interpret phi: particular_struct_injection \<Gamma>\<^sub>x \<Gamma> \<phi> 
    using A(3) .
  obtain f :: \<open>'a \<Rightarrow> ZF\<close> where f: \<open>inj f\<close> 
    using phi.src.injection_to_ZF_exist by blast
  have \<open>phi.src.\<Gamma> = \<Gamma>\<^sub>x\<close> by auto
  have \<open>particular_struct_bijection_1 \<Gamma>\<^sub>x f\<close> using f
    apply (subst \<open>phi.src.\<Gamma> = \<Gamma>\<^sub>x\<close>[symmetric])
    apply (intro phi.src.inj_morph_img_isomorphism)
    subgoal using inj_on_subset by blast
    using inj_on_id by blast
  then interpret gamma_x: 
      particular_struct_bijection_1 \<Gamma>\<^sub>x f  
    by blast
  have \<open>particular_struct_injection (MorphImg f \<Gamma>\<^sub>x) \<Gamma>\<^sub>x gamma_x.inv_morph\<close>    
    using particular_struct_bijection_def by blast
  then interpret gamma_x_inv: 
    particular_struct_injection \<open>MorphImg f \<Gamma>\<^sub>x\<close> \<Gamma>\<^sub>x gamma_x.inv_morph .
  have \<open>particular_struct_injection (MorphImg f \<Gamma>\<^sub>x) \<Gamma> (\<phi> \<circ> gamma_x.inv_morph)\<close>
    apply (intro particular_struct_injection_comp[of _ \<Gamma>\<^sub>x])
    by (intro_locales)
  then interpret phi_gamma_x_inv: 
    particular_struct_injection 
       \<open>MorphImg f \<Gamma>\<^sub>x\<close> \<Gamma> \<open>\<phi> \<circ> gamma_x.inv_morph\<close> 
       \<open>TYPE(ZF)\<close> \<open>TYPE('p)\<close> .
  have R1: \<open>MorphImg f \<Gamma>\<^sub>x \<lless>\<^bsub>\<phi> \<circ> gamma_x.inv_morph\<^esub> \<Gamma>\<close>    
    using injectives_I[
           OF phi_gamma_x_inv.particular_struct_injection_axioms]
    by blast
  have R2: \<open>\<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub>\<close>           
    using phi.particular_struct_morphism_axioms by blast
  have R3[simp]: \<open>\<phi> y = x\<close> 
    using A(4)[OF _ R2,simplified,of y,simplified] A(2) by metis
  have R4: \<open>f y \<in> gamma_x_inv.src.\<P>\<close> using A(2) by blast
  
  have R5: \<open>f y \<midarrow>MorphImg f \<Gamma>\<^sub>x,\<phi> \<circ> gamma_x.inv_morph\<rightarrow>\<^sub>1 x\<close> 
  proof (intro anchorsI A(1) R1 R4)
    fix \<sigma> z
    assume as: \<open>z \<in> gamma_x_inv.src.\<P>\<close> \<open>\<sigma> \<in> Morphs\<^bsub>MorphImg f \<Gamma>\<^sub>x,\<Gamma>\<^esub>\<close>
    interpret sigma: 
      particular_struct_morphism \<open>MorphImg f \<Gamma>\<^sub>x\<close> \<Gamma> \<sigma> 
      using as(2) by blast
    interpret 
      particular_struct_morphism \<Gamma>\<^sub>x \<Gamma> \<open>\<phi> \<circ> gamma_x.inv_morph \<circ> f\<close>                                 
      apply (intro particular_struct_morphism_comp[
                    of _ \<open>MorphImg f \<Gamma>\<^sub>x\<close>])
      by intro_locales
    
    interpret sigma_f: 
      particular_struct_morphism \<Gamma>\<^sub>x \<Gamma> \<open>\<sigma> \<circ> f\<close>                                      
      apply (intro particular_struct_morphism_comp[of _ \<open>MorphImg f \<Gamma>\<^sub>x\<close>])
      by intro_locales
    have RR1: \<open>\<sigma> \<circ> f \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub>\<close>       
      using sigma_f.particular_struct_morphism_axioms by blast
    have I1: \<open>gamma_x.inv_morph (f x) = x\<close> if \<open>x \<in> phi.src.\<P>\<close> for x
      using that  by simp
    have I2: \<open>f (gamma_x.inv_morph x) = x\<close> if \<open>x \<in> gamma_x.tgt.\<P>\<close> for x
      using that  by simp
    show \<open>\<sigma> z = x \<longleftrightarrow> z = f y\<close>
      supply R =  I1 I2 A(4)[OF _ RR1,simplified] R3 as(1) A(2) 
      apply (intro iffI)
      subgoal using R 
        by (metis gamma_x_inv.morph_preserves_particulars)
      using R by blast
  qed
  have R6: \<open>MorphImg f \<Gamma>\<^sub>x \<in> IsoModels\<^bsub>\<Gamma>\<^sub>x,TYPE(ZF)\<^esub>\<close>    
    using gamma_x.particular_struct_bijection_1_axioms by blast
  then show ?thesis using R5 by blast
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> anchored_particulars_are_particulars: \<open>\<P>\<^sub>\<down> \<subseteq> \<P>\<close> 
  by blast

end

end