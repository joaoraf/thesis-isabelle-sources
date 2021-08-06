text_raw \<open>\subsection[Isomorphically Unique Particulars]{Isomorphically Unique Particulars\isalabel{subsec:isomorphical-uniqueness}}\<close>

theory IsomorphicalUniqueness
  imports ParticularStructureMorphisms 
begin

context ufo_particular_theory_sig
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We can study a particular's formal properties in a particular structure through the various possible mappings it may have through morphisms that initiate or target
  that particular structure. One of these properties if that of being isomorphically
  unique, defined by considering the bijective morphisms from the particular structure.

  The existence of a bijective morphism between particular structures \<open>\<Gamma>\<^sub>1\<close> and
  \<open>\<Gamma>\<^sub>2\<close> implies that both structures express the same configuration, 
  differing, if they do, only in representation of particulars.

  We say that a particular \<open>x\<close> is isomorphically unique in a particular structure
  \<open>\<Gamma>\<close> if and only if, for every bijective morphism \<open>\<phi>\<close> from \<open>\<Gamma>\<close> to some  
  particular structure \<open>\<Gamma>'\<close>, and for every morphism \<open>\<sigma>\<close> from \<open>\<Gamma>\<close> to \<open>\<Gamma>'\<close>,
  \<open>\<phi>\<close> and \<open>\<sigma>\<close> agree with respect to \<open>x\<close>. 

  Since particular structures are polymorphic on the type of particulars
  and Isabelle/HOL does not allow quantification over types, we need to
  define the notion of an isomorphically unique particular using some 
  fixed choice of representation for the target particular structures.
  We chose here to use the \<open>ZF\<close> Isabelle/HOL type of ZF sets as the 
  target representation, assuming that any domain of particulars is
  representable using ZF sets.
  
  Thus, the formal definition of isomorphically unique particulars is:
\<close>

definition isomorphically_unique_particulars (\<open>\<P>\<^sub>\<simeq>\<^sub>!\<close>)
  where \<open>\<P>\<^sub>\<simeq>\<^sub>! \<equiv> { x . x \<in> \<P> \<and> ( 
          \<forall>\<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub>. \<forall>\<sigma> \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<phi> \<Gamma>\<^esub>.
          \<forall>y \<in> \<P>.
          \<sigma> y = \<phi> x \<longleftrightarrow> y = x)}\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphically_unique_particulars_I[intro!]:
  assumes \<open>x \<in> \<P>\<close>
    \<open>\<And>\<phi> \<sigma> y. \<lbrakk> \<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> ; \<sigma> \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<phi> \<Gamma>\<^esub>
            ; y \<in> \<P> \<rbrakk>
      \<Longrightarrow> \<sigma> y = \<phi> x \<longleftrightarrow> y = x\<close>
  shows \<open>x \<in> \<P>\<^sub>\<simeq>\<^sub>!\<close>
  using assms by (auto simp: isomorphically_unique_particulars_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphically_unique_particulars_E[elim!]:
  assumes \<open>x \<in> \<P>\<^sub>\<simeq>\<^sub>!\<close>
  obtains \<open>x \<in> \<P>\<close>
    \<open>\<And>\<phi> \<sigma> y. \<lbrakk> \<phi> \<in> BijMorphs1\<^bsub>\<Gamma>,TYPE(ZF)\<^esub> ; \<sigma> \<in> Morphs\<^bsub>\<Gamma>,MorphImg \<phi> \<Gamma>\<^esub> ; y \<in> \<P> \<rbrakk>
      \<Longrightarrow> \<sigma> y = \<phi> x \<longleftrightarrow> y = x\<close>  
  using assms by (auto simp: isomorphically_unique_particulars_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphically_unique_particulars_are_particulars: \<open>\<P>\<^sub>\<simeq>\<^sub>! \<subseteq> \<P>\<close>
  by auto

end

end
