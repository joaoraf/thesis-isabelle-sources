text_raw \<open>\section[Particulars and Possible Worlds]{Particulars and Possible Worlds\isalabel{sec:possible-worlds}}\<close>

theory \<^marker>\<open>tag aponly\<close> PossibleWorlds
  imports  Main "../Misc/Common" 
begin \<^marker>\<open>tag aponly\<close>      

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The most basic notion in UFO, and in the UFO derived ontology described in this thesis, is the 
  concept of a @{emph \<open>particular\<close>} as an entity, or being, that enjoy the property of existing, 
  either in actuality or, at least, in potential.

  Given a domain of discourse that delineates a scope particulars, any maximal configuration of 
  its elements that is considered possible, in the sense that it is conceivable that the reality 
  they represent could possibly obtain, is called a @{emph \<open>possible world\<close>}.

  As was explained in \autoref{cha:preliminary-review}, the representation of an ontological commitment requires a 
  suitable representation of the possible configurations of the reality towards which the commitment 
  is made. Thus, the notion of a possible world and of the delineation of possibilities given by 
  the set of all possible worlds is the basis of the ontological theory provided in this chapter.

  This section presents the structure of particulars and possible worlds that is used throughout the 
  thesis. The structure is initially presented in its most basic form, lacking elements that can be 
  used to characterize the particulars and describe their inter-relationships. These elements shall
  be introduced gradually on the next sections.

  The only information given by this structure is the composition of the set of particulars, and
  their potential co-existence, i.e. two or more particulars are deemed possibly co-existants just
  in case there is at least one possible world which contain all of them. As such, the representation 
  of a possible world is simply a set of particulars: 
\<close>
text_raw\<open>\par\<close>
type_synonym 'p world =  \<open>'p set\<close>

locale \<^marker>\<open>tag aponly\<close> possible_worlds_sig =
  fixes \<W> :: \<open>'p world set\<close> 
    and Typ\<^sub>p :: \<open>'p itself\<close>
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The theory of possible worlds described in this section has the following signature: 
\<close>

text_raw \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{tabular}{ll}
Type & Denotation \tabularnewline
\hline
$@{typ "'p"}$ & particulars \tabularnewline
$@{typ "'p world"}$ & possible worlds (sets of particulars) \tabularnewline
$@{typ "'p world set"}$ & sets of possible worlds \tabularnewline
\end{tabular}

\par

\begin{tabular}{lll}
Symbol & Type & Denotation \tabularnewline
\hline
$@{term "\<W>"}$ & $@{typeof \<open>\<W>\<close>}$ & set of possible worlds \tabularnewline
\end{tabular}
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The set of \emph{particulars}, written as @{text \<open>\<P>\<close>}, consists in the set of all 
  particulars that compose all possible worlds:
\<close>
text_raw\<open>\par\<close>
definition \<P> :: \<open>'p set\<close> where \<open>\<P> \<equiv> \<Union>\<W>\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Given two particulars, \<open>x\<close> and \<open>y\<close>, we say that \<open>x\<close> is 
  \emph{existentially dependent upon} \<open>y\<close>, written as \<open>ed x y\<close>, whenever the existence of
  the former implies the existence of the later:\<close>
text_raw\<open>\par\<close>
definition ed :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close> 
  where \<open>ed x y \<equiv> x \<in> \<P> \<and> y \<in> \<P> \<and> 
                  (\<forall>w \<in> \<W>. x \<in> w \<longrightarrow> y \<in> w)\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
 Given two particulars, \<open>x\<close> and \<open>y\<close>, we say that \<open>x\<close> and \<open>y\<close> are 
  \emph{existentially interdependent}, written as \<open>interdep x y\<close>, 
  if they are existentially dependent upon each other:
\<close>
text_raw\<open>\par\<close>
definition interdep :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close> 
  where \<open>interdep x y \<equiv> ed x y \<and> ed y x\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Given two particulars, \<open>x\<close> and \<open>y\<close>, we say that \<open>x\<close> and \<open>y\<close> are 
  \emph{existentially independent}, written as \<open>indep x y\<close>, if neither
  the existence of \<open>x\<close> nor the existence of \<open>y\<close> imply the existence of
  the other:
\<close>
text_raw\<open>\par\<close>
definition indep :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close> 
  where \<open>indep x y \<equiv> x \<in> \<P> \<and> y \<in> \<P> 
                   \<and> \<not> ed x y \<and> \<not> ed y x\<close>

end \<^marker>\<open>tag aponly\<close>

locale \<^marker>\<open>tag aponly\<close> possible_worlds =  
    possible_worlds_sig where Typ\<^sub>p = \<open>Typ\<^sub>p\<close>
  for 
    Typ\<^sub>p :: \<open>'p itself\<close> +
  assumes \<^marker>\<open>tag aponly\<close>
    injection_to_ZF_exist: \<open>\<exists>(f :: 'p \<Rightarrow> ZF). inj f\<close> and  
    at_least_one_possible_world: \<open>\<W> \<noteq> \<emptyset>\<close> and    
    particulars_do_not_exist_in_some_world: 
      \<open>x \<in> \<P> \<Longrightarrow> \<exists>w\<in>\<W>. x \<notin> w\<close> and
    undefined_not_in_particulars:
      \<open>w \<in> \<W> \<Longrightarrow> undefined \<notin> w\<close>
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The set of possible worlds is constrained by the following axioms:

  \begin{axiom}[$@{thm_name at_least_one_possible_world}$]
      Since at least one possible configuration is deemed possible, e.g. that of actuality, 
      at least one possible world must exist, even if its empty, i.e. even if no particulars 
      exist in actuality:

      \[ @{thm at_least_one_possible_world} \]

  \end{axiom}

  \begin{axiom}[@{thm_name particulars_do_not_exist_in_some_world}]
      No particular is deemed necessary, or, in other words, every particular’s existence is 
      @{emph \<open>contigent\<close>}. This restriction was added to exclude entities that could be considered 
      to exist by definition, such as natural numbers, logical formulas, etc., since such entities 
      are better described by specific axiomatic theories instead of by an ontological theory 
      that carry the added structure of possible existence and non-existence:

      \[ @{thm particulars_do_not_exist_in_some_world} \]
  \end{axiom}

  \begin{axiom}[@{thm_name injection_to_ZF_exist}]
      The domain from which particulars are drawn is not “too big”, in the sense that it can be 
      represented by [glos:Zermelo-Fraenkel] sets through at least one injective function. This 
      constraint is required to circumvent some limitations of Isabelle/HOL type system regarding 
      proofs that exhibit type polymorphism:

      \[ @{thm injection_to_ZF_exist [show_types]} \]
  \end{axiom}  
 \<close>
text_raw\<open>\par\<close>
end \<^marker>\<open>tag aponly\<close>

context \<^marker>\<open>tag (proof) aponly\<close> possible_worlds_sig
begin  \<^marker>\<open>tag (proof) aponly\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> \<P>_I[intro]: 
  assumes \<open>w \<in> \<W>\<close> \<open>x \<in> w\<close> 
  shows \<open>x \<in> \<P>\<close> 
  using assms \<P>_def by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> \<P>_E[elim]:
  assumes \<open>x \<in> \<P>\<close> 
  obtains w where \<open>w \<in> \<W>\<close> \<open>x \<in> w\<close>
  using assms \<P>_def by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> edI[intro!]: 
  assumes 
      \<open>x \<in> \<P>\<close> \<open>y \<in> \<P>\<close> \<open>\<And>w. \<lbrakk> w \<in> \<W> ; x \<in> w \<rbrakk> \<Longrightarrow> y \<in> w\<close>
  shows \<open>ed x y\<close> 
  using ed_def assms by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> edE[elim!]:
  assumes \<open>ed x y\<close> 
  obtains \<open>x \<in> \<P>\<close> \<open>y \<in> \<P>\<close> 
          \<open>\<And>w. \<lbrakk> w \<in> \<W> ; x \<in> w \<rbrakk> \<Longrightarrow> y \<in> w\<close>
  using ed_def assms by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> edD:
  assumes \<open>ed x y\<close> \<open>w \<in> \<W>\<close> \<open>x \<in> w\<close>
  shows \<open>y \<in> w\<close>
  using ed_def assms by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> ed_scope:
  assumes \<open>ed x y\<close>
  shows \<open>x \<in> \<P>\<close> \<open>y \<in> \<P>\<close>
  using ed_def assms by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> indepI[intro!]: 
  assumes \<open>x \<in> \<P>\<close> \<open>y \<in> \<P>\<close> \<open>\<not> ed x y\<close> \<open>\<not> ed y x\<close> 
  shows \<open>indep x y\<close> 
  using assms by (auto simp: indep_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> indepI1: 
  fixes x y w\<^sub>x w\<^sub>y
  assumes \<open>w\<^sub>x \<in> \<W>\<close> \<open>x \<in> w\<^sub>x\<close> \<open>y \<notin> w\<^sub>x\<close> 
          \<open>w\<^sub>y \<in> \<W>\<close> \<open>y \<in> w\<^sub>y\<close> \<open>x \<notin> w\<^sub>y\<close>   
  shows \<open>indep x y\<close> 
  using assms by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> indepE[elim!]: 
  assumes \<open>indep x y\<close> 
  obtains \<open>x \<in> \<P>\<close> \<open>y \<in> \<P>\<close> \<open>\<not> ed x y\<close>  \<open>\<not> ed y x\<close> 
  using assms 
  by (auto simp: indep_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> ed_refl: 
  \<open>x \<in> \<P> \<Longrightarrow> ed x x\<close> 
  by (auto simp: ed_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> ed_trans: 
  \<open>\<lbrakk> ed x y ; ed y z \<rbrakk> \<Longrightarrow> ed x z\<close>
  by (auto simp: ed_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> interdep_refl: 
  \<open>x \<in> \<P> \<Longrightarrow> interdep x x\<close>
  by (auto simp: interdep_def ed_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> interdep_symm[sym]: 
  \<open>interdep x y \<Longrightarrow> interdep y x\<close>
  by (auto simp: interdep_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> interdep_trans: 
  assumes \<open>interdep x y\<close> \<open>interdep y z\<close>
  shows \<open>interdep x z\<close>
  using assms by (simp add: interdep_def ; metis ed_trans)

lemma \<^marker>\<open>tag (proof) aponly\<close> indep_sym[sym]: 
  \<open>indep x y \<Longrightarrow> indep y x\<close>
  by blast

end \<^marker>\<open>tag (proof) aponly\<close>

context \<^marker>\<open>tag (proof) aponly\<close> possible_worlds
begin \<^marker>\<open>tag (proof) aponly\<close>

lemmas \<^marker>\<open>tag (proof) aponly\<close> just_possible_worlds_axioms = 
  at_least_one_possible_world
  particulars_do_not_exist_in_some_world

lemmas \<^marker>\<open>tag (proof) aponly\<close> all_possible_worlds_axioms = 
  just_possible_worlds_axioms

lemma \<^marker>\<open>tag (proof) aponly\<close> worlds_are_made_of_particulars: 
  \<open>w \<in> \<W> \<Longrightarrow> w \<subseteq> \<P>\<close> 
  by (auto simp: \<P>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> particulars_exist_in_some_world: 
  \<open>x \<in> \<P> \<Longrightarrow> \<exists>w\<in>\<W>. x \<in> w\<close> 
  by (auto simp: \<P>_def)    
  
lemma \<^marker>\<open>tag (proof) aponly\<close> non_empty_particulars_at_least_two_worlds:
    \<open>\<P> \<noteq> \<emptyset> \<Longrightarrow> \<exists>w\<^sub>1\<in>\<W>. \<exists>w\<^sub>2\<in>\<W>. w\<^sub>1 \<noteq> w\<^sub>2\<close>
proof -
  assume \<open>\<P> \<noteq> \<emptyset>\<close>
  then obtain x where \<open>x \<in> \<P>\<close> 
    by blast 
  then show \<open>?thesis\<close> 
    using 
      particulars_exist_in_some_world 
      particulars_do_not_exist_in_some_world  
    by metis
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> 
  no_empty_worlds_imp_two_particulars:
  \<open>\<emptyset> \<notin> \<W> \<Longrightarrow> \<exists>x\<^sub>1\<in>\<P>. \<exists>x\<^sub>2\<in>\<P>. x\<^sub>1 \<noteq> x\<^sub>2\<close>
proof -
  assume \<open>\<emptyset> \<notin> \<W>\<close>
  then obtain w\<^sub>1 where \<open>w\<^sub>1 \<in> \<W>\<close> \<open>w\<^sub>1 \<noteq> \<emptyset>\<close> 
    using at_least_one_possible_world by blast
  then obtain x\<^sub>1 where \<open>x\<^sub>1 \<in> w\<^sub>1\<close> by blast
  then have \<open>x\<^sub>1 \<in> \<P>\<close> 
    using \<open>w\<^sub>1 \<in> \<W>\<close> worlds_are_made_of_particulars 
    by blast
  then obtain w\<^sub>2 where \<open>w\<^sub>2 \<in> \<W>\<close> \<open>w\<^sub>2 \<noteq> \<emptyset>\<close> \<open>x\<^sub>1 \<notin> w\<^sub>2\<close>
    using particulars_do_not_exist_in_some_world
          \<open>\<emptyset> \<notin> \<W>\<close>
    by blast
  then obtain x\<^sub>2 where \<open>x\<^sub>2 \<in> w\<^sub>2\<close> \<open>x\<^sub>2 \<noteq> x\<^sub>1\<close> by blast
  then have \<open>x\<^sub>2 \<in> \<P>\<close> 
    using worlds_are_made_of_particulars \<open>w\<^sub>2 \<in> \<W>\<close> 
    by blast
  then show \<open>?thesis\<close>
    using \<open>x\<^sub>1 \<in> \<P>\<close> \<open>x\<^sub>2 \<noteq> x\<^sub>1\<close> by blast
qed

end \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The full Isabelle/HOL source for this theory describes various lemmas that can be 
  derived from these axioms and definitions. We include here some of the
  most relevant, omitting the respective proofs, which can be found in 
  \autoref{ape:sec:possible-worlds}. 

  The following lemmas follow exclusively from the definition of the respective relations:
\<close>
text_raw\<open>\par\<close>
context \<^marker>\<open>tag aponly\<close> possible_worlds_sig 
begin \<^marker>\<open>tag aponly\<close>
 
text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}[@{thm_name ed_refl}, @{thm_name ed_trans}]
      Existential dependency is a [glos:pre-order], i.e it is a reflexive and transitive relation:
      \begin{align*}
       @{thm ed_refl [no_vars]} \\
       @{thm ed_trans [no_vars]} \\
      \end{align*}
  \end{lemma}
  
   
  \begin{lemma}[@{thm_name interdep_refl}, @{thm_name interdep_symm}, @{thm_name interdep_trans}]
    Existential interdependency is an [glos:equivalence-relation], i.e. it is reflexive, symmetric 
      and transitive:    
      \begin{align*}
      @{thm interdep_refl [no_vars]} \\
      @{thm interdep_symm [no_vars]} \\
      @{thm interdep_trans [no_vars]} \\
     \end{align*}
  \end{lemma}
   
  \begin{lemma}[@{thm_name indep_sym}]
    Existential independency is a symmetric relation:
      \[ @{thm indep_sym [no_vars]} \]
  \end{lemma}
\<close>
text_raw\<open>\par\<close>
end \<^marker>\<open>tag aponly\<close>

context \<^marker>\<open>tag aponly\<close> possible_worlds 
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
   From the axioms, we can derive the following lemmas:
\<close>
 
text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}[@{thm_name non_empty_particulars_at_least_two_worlds}]
      If there is at least one particular, then there must be at least two distinct possible worlds:       
      \[ @{thm non_empty_particulars_at_least_two_worlds [no_vars]} \] 
  \end{lemma}

  \begin{lemma}[@{thm_name no_empty_worlds_imp_two_particulars}]
      If no empty possible worlds exist, i.e. it isn’t possible for a reality void of existing 
      things to obtain, then there are at least two distinct particulars:  
    \[ @{thm no_empty_worlds_imp_two_particulars [no_vars]} \] 
  \end{lemma}   
\<close>
text_raw\<open>\par\<close>
end \<^marker>\<open>tag aponly\<close>

subsection \<open>Modes of Existence\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The first distinction that UFO makes between particulars is one based on their 
  [glos: modes of existence]: a particular is either an @{emph \<open>endurant\<close>}, i.e. a being that exists 
  as a complete entity in every instant of time in which it is considered present, or an 
  @{emph \<open>event\<close>}, also called a @{emph \<open>perdurant\<close>}, i.e. a being that is observable as a whole 
  only when the whole time interval of its existence is considered.

  Since this thesis focuses on endurants, we exclude the set of events from the set of 
  particulars, by considering the later a synonym for the set of endurants:\<close>
text_raw\<open>\par\<close>
abbreviation (in possible_worlds_sig) 
  endurants (\<open>\<E>\<close>) where \<open>\<E> \<equiv> \<P>\<close>

end \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In the following sections, the structure of possible worlds is enriched with elements that 
  allow a minimal representation of qualities of particulars and of relations between them.\<close>
text_raw\<open>\par\<close>