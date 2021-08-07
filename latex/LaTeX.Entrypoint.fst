module LaTeX.Entrypoint
//!add-dir . ../src/core

module Prettier = LaTeX.Prettier

open Main
/// \documentclass{llncs}
/// \input{latex/preamble.tex}
/// \newcommand{\orcidlink}[1]{\href{https://orcid.org/#1}{\includegraphics[height=0.6em]{latex/orcid.pdf}}}
/// 
/// \begin{document}
/// \author{%
/// Lucas Franceschino\inst{1}
/// \,\orcidlink{0000-0002-5683-0199}
/// \and %
/// David Pichardie\inst{2}
/// \,\orcidlink{0000-0002-2504-1760}
/// \and %
/// Jean-Pierre Talpin\inst{1}
/// \,\orcidlink{0000-0002-0556-4265}
/// }
/// \institute{%
/// ${}^1$~INRIA Rennes, France %
/// % \and %
/// ~~~${}^2$~ENS Rennes, France%
/// }
/// 
/// \maketitle{}
/// \input{latex/abstract.tex}
/// \input{latex/introduction.tex}

/// \section{$\AbIntImp{}$: a Small Imperative Language}
//!open LangDef

/// \section{Operational Semantics}
/// \label{abint:section:operational-sematics}
//!open OperationalSemantic

/// \section{Abstract Domains}
/// \label{abint:section:abstract-domains}
//!open ADom

/// \section{An Example of Abstract Domain: Intervals}
/// \label{abint:section:intervals}
//!open Interval
 
/// \section{Specialized Abstract Domains}
/// \label{abint:section:specialized-adoms}

/// Abstract domains are defined in Section~\ref{abint:section:abstract-domains} as
/// lattices equipped with a sound concretization operation.

/// Our abstract interpreter analyses $\AbIntImp{}$ programs: its
/// expressions are numerical, and $\AbIntImp{}$ is equipped with a memory.
/// Thus, this section defines two specialized abstract domains: one
/// for numerical abstractions, and another one for memory
/// abstractions.
 
/// \subsection{Numerical Abstract Domains}
//!open ADom.Num

/// \subsection{Memory Abstract Domains}
//!open ADom.Mem

/// \section{A Weakly-Relational Abstract Memory}
/// \label{abint:section:weakly-rel-amem}
//!open AMem
///
//!open AMem.ADom

/// \section{Statement Abstract Interpretation}
/// \label{abint:section:stmt-ab-int}
//!open AbstractSemantic

/// \input{latex/related-work.tex}
/// \input{latex/conclusion.tex}
// List of hidden definitions:{ {hidden-report}};

/// \newpage
/// \printglossary[type=\acronymtype]
/// \bibliographystyle{latex/splncs04}
/// \bibliography{latex/main}
/// 
/// \end{document}

