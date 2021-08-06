text_raw \<open>\section[Individuality]{Individuality\isalabel{sec:individuality}}\<close>

theory Individuality
  imports "../ParticularStructures/CollapsibleParticulars"
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In \cite{UFO}, Guizzardi explains that the version of UFO 
  presented there ``exclude the so-called quasi-objects, i.e.,
  individuals that have determinate countability but indeterminate
  identity''. The reason given for such decision is that there
  is an ``associated belief that quasi-objects do not exist in the
  macroscopic level''. However, in sequence, Guizzardi admits that
  quasi-objects could be included by extending the theory
  appropriately.

  In this section, we provide a formal definition for what
  a quasi-object, or what we call here a \emph{particular with
  individuality} is, or what differentiates it from a particular
  that lacks individuality. The approach here is not to characterize
  a particular with individuality as one for which a ``determinate
  countability'' exists \cite{UFO}, but, instead, to characterize
  the \emph{individuality} as a structural property of the particular,
  i.e. a consequence of existing in a particular configuration of things.
    
  First, lets define the particulars with individuality in a UFO 
  particular structure as being exactly those particulars that are \emph{non-collapsible}:
\<close>
text_raw \<open>\par\<close>
context ufo_particular_theory_sig
begin

abbreviation particularsWithIndividuality (\<open>\<P>\<^sub>i\<^sub>n\<^sub>d\<close>) where
  \<open>\<P>\<^sub>i\<^sub>n\<^sub>d \<equiv> \<P>\<^sub>n\<^sub>c\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  To see what this definition implies, consider two simple examples,
  based on Black's twin spheres example \cite{black45}:

  \begin{enumerate}
  \item Let $U_1$ be a universe in which spheres $S_1$ and $S_2$ exist.
        For all intentions and purposes, $S_1$ and $S_2$ have the same
        intrinsic properties, e.g. radius, color, mass, etc. No 
        material relation is recorded between the two spheres;
  \item Let $U_2$ be a universe in which spheres $S_1$ and $S_2$ exist.
        For all intentions and purposes, $S_1$ and $S_2$ have the same
        intrinsic properties, e.g. radius, color, mass, etc. The
        spheres $S_1$ and $S_2$ are 1 km apart from each other.        
  \end{enumerate}

  In the first configuration spheres $S_1$ and $S_2$ are \emph{collapsible},
  i.e. they can be mapped to the same particular (e.g.$S_1$) by a particular
  structure morphism that preserves the formal properties of the particulars.
  In other words, there is no evidence, in the first example, that spheres
  $S_1$ and $S_2$ are in fact, distinct, since no formal property is lost by
  considering them to be the same\todo{João P.: please include example of collapsable particulars in a practical setting - for example, as the result of a modeling issue. Should we force the modeller to be explicit about these properties? }.

  Contrast this with the second example, for which no such morphism can be
  found, due to the existence of a distance relation (of 1km) between the
  spheres: if we consider them to be a single sphere, we arrive at an 
  impossible situation of having a physical object being 1km apart from
  itself.  
\<close>
text_raw \<open>\par\<close>
lemmas particularsWithIndividualityI = nonCollapsibleParticularsI

lemmas particularsWithIndividualityE = nonCollapsibleParticularsE

lemmas particularsWithIndividuality_iff = nonCollapsibleParticulars_iff

lemmas substantialsWithIndividualitySubset = 
  nonCollapsibleParticularsAreParticulars

end

end