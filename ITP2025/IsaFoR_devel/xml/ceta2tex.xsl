<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:ceta="http://cl-informatik.uibk.ac.at/software/ceta" 
  version="1.0">
<xsl:output method="text"/>
<xsl:strip-space elements="ceta:arg"/>
    
<xsl:template match="/ceta:proof">
  <xsl:variable name="mode">
    <xsl:choose>
      <xsl:when test="count(/ceta:proof/ceta:loop) + count(/ceta:proof/ceta:notWellFormed) = 0">Termination Proof</xsl:when>
      <xsl:otherwise>Nontermination Proof</xsl:otherwise>
    </xsl:choose>
  </xsl:variable>
\documentclass{scrartcl}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}

\newcommand{\CeTA}{\textsf{C\kern-0.2exe\kern-0.5exT\kern-0.5exA}}
\newcommand\cetaHeading[1]{\noindent{\usekomafont{title}#1}
  \smallskip

}
\newcommand\fun[1]{\textsf{#1}}
\newcommand\var[1]{\textit{#1}}
\newcommand\dpFun[1]{\textsf{#1}}
\newcommand\lab[1]{\textsf{#1}}

\title{<xsl:value-of select="$mode"/>}
\author{\CeTA}

\begin{document}
%\maketitle
\centerline{\LARGE\usekomafont{title}<xsl:value-of select="$mode"/>}
\begin{proof}\mbox{}
<xsl:apply-templates>
  <xsl:with-param name="indent" select="1"/>
</xsl:apply-templates>
\end{proof}
\end{document}
</xsl:template>    
        
<xsl:template match="ceta:notWellFormed">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> Not Well-Formed}
  The TRS violates one of the two variable conditions. Thus, it is not terminating.
</xsl:template>
    
    
<xsl:template match="ceta:loop">
  <xsl:param name="indent"/>
  <xsl:variable name="context" select="count(ceta:box) = 0"/>
  <xsl:variable name="subst" select="count(ceta:substitution/ceta:substEntry) &gt; 0"/>
  \cetaHeading{<xsl:value-of select="$indent"/> Loop}
  The following loop proves nontermination:            
    \begin{align*}
    <xsl:for-each select="*">
      <xsl:if test="position() &gt; 2">
        <xsl:choose>
          <xsl:when test="position() = 3">
            <xsl:text>t &amp;=</xsl:text>
          </xsl:when>
          <xsl:otherwise>
            &amp;\to
          </xsl:otherwise>
        </xsl:choose>
      <xsl:apply-templates select="."/>\\
      </xsl:if>
    </xsl:for-each>
    <xsl:text>&amp;\to </xsl:text>
    <xsl:if test="$context">C[</xsl:if>t<xsl:if test="$subst">\sigma</xsl:if><xsl:if test="$context">]</xsl:if>
  \end{align*}
  <xsl:if test="$subst or $context">
      where
  </xsl:if>
  <xsl:if test="$subst">
      <xsl:text>$\sigma = </xsl:text><xsl:apply-templates select="ceta:substitution"/><xsl:text>$</xsl:text>
  </xsl:if>
  <xsl:if test="$subst and $context">
    <xsl:text> and</xsl:text>
  </xsl:if>            
  <xsl:if test="$context">
      $C = <xsl:apply-templates select="*[2]"/><xsl:text>$</xsl:text>
  </xsl:if>
  <xsl:text>.</xsl:text>
</xsl:template>
    
<xsl:template match="ceta:type">
  <xsl:choose>
    <xsl:when test="count(ceta:linearPolynomial) &gt; 0">
      <xsl:text> linear polynomial</xsl:text>
    </xsl:when>
    <xsl:otherwise>
      <xsl:text>unknown</xsl:text>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>
    
<xsl:template match="ceta:domain">
  <xsl:choose>
    <xsl:when test="count(ceta:naturals) &gt; 0">
      <xsl:text>the naturals</xsl:text>
    </xsl:when>
    <xsl:otherwise>
      <xsl:text>an unknown domain</xsl:text>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>
    
<xsl:template name="genVars">
  <xsl:param name="n"/>
  <xsl:choose>
    <xsl:when test="$n = 0"/>
    <xsl:when test="$n = 1">
      <xsl:text>(x_1)</xsl:text>
    </xsl:when>
    <xsl:when test="$n = 2">
      <xsl:text>(x_1,x_2)</xsl:text>
    </xsl:when>
    <xsl:when test="$n = 3">
      <xsl:text>(x_1,x_2,x_3)</xsl:text>
    </xsl:when>
    <xsl:otherwise>
      <xsl:text>(x_1,\dots,x_{</xsl:text><xsl:value-of select="$n"/><xsl:text>})</xsl:text>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>
    
<xsl:template match="ceta:linearPolynomial">
  <xsl:if test="ceta:constant/ceta:number/text() &lt; '0'">
    <xsl:text>\max(</xsl:text>
  </xsl:if>
  <xsl:for-each select="ceta:coefficient[ceta:natural/text() != '0']">
    <xsl:if test="position() != 1"><xsl:text>+</xsl:text> </xsl:if>
    <xsl:if test="ceta:natural/text() != '1'"><xsl:apply-templates select="."/></xsl:if>
    <xsl:text>x_{</xsl:text><xsl:value-of select="position()"/><xsl:text>}</xsl:text>
  </xsl:for-each>        
  <xsl:if test="ceta:constant/ceta:number/text() &lt; '0'">
    <xsl:apply-templates select="ceta:constant"/>
    <xsl:text>,0)</xsl:text>
  </xsl:if>
  <xsl:if test="ceta:constant/ceta:number/text() &gt; '0'">
    <xsl:if test="count(ceta:coefficient[ceta:natural/text() != 0]) &gt; 0">
      <xsl:text>+</xsl:text>
    </xsl:if>
    <xsl:apply-templates select="ceta:constant"/>
  </xsl:if>
  <xsl:if test="ceta:constant/ceta:number/text() = '0'">
    <xsl:if test="count(ceta:coefficient[ceta:natural/text() != 0]) = 0">
      <xsl:apply-templates select="ceta:constant"/>                
    </xsl:if>            
  </xsl:if>
</xsl:template>

<xsl:template match="ceta:constant">
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="ceta:coefficient">        
  <xsl:apply-templates/>
</xsl:template>
    
<xsl:template match="ceta:interpretation">
  <xsl:apply-templates select="*[1]"/> 
  interpretation over 
  <xsl:apply-templates select="*[2]"/>
  \begin{align*}
    <xsl:for-each select="ceta:interpret">
      <xsl:text>[</xsl:text><xsl:apply-templates select="ceta:name"/><xsl:text>]</xsl:text>
      <xsl:call-template name="genVars">
        <xsl:with-param name="n" select="ceta:arity"/>
      </xsl:call-template>
      <xsl:text> &amp;= </xsl:text>
      <xsl:apply-templates select="ceta:function"/>\\
    </xsl:for-each>
    <xsl:text>[f](x_1,\dots,x_n) &amp;= x_1 + \dots + x_n + 1</xsl:text>\\
      &amp;\text{for all other symbols f of arity n}
  \end{align*}
</xsl:template>
    
<xsl:template match="ceta:dpTrans">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> Dependency Pair Transformation}
  <xsl:choose>
  <xsl:when test="count(ceta:dps/ceta:rules/ceta:rule) &gt; 0">
    The following set of initial dependency pairs has been identified:
    <xsl:apply-templates select="ceta:dps/*"/>
    <xsl:apply-templates select="*[2]">
      <xsl:with-param name="indent" select="concat($indent,'.1')"/>
    </xsl:apply-templates>
  </xsl:when>
  <xsl:otherwise>
    The set of initial dependency pairs is empty, and hence the TRS is
    terminating. 
  </xsl:otherwise>
  </xsl:choose>
</xsl:template>
    
<xsl:template match="ceta:unlabProc">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> Unlabeling Processor}
  After removing one layer of labels
  we obtain the set of pairs
  <xsl:apply-templates select="ceta:dps/*"/>
  and the set of rules        
  <xsl:apply-templates select="ceta:trs/*"/>
  
  \bigskip
  <xsl:apply-templates select="*[3]">
    <xsl:with-param name="indent" select="concat($indent, '.1')"/>
  </xsl:apply-templates>
</xsl:template>

<xsl:template match="ceta:semlabProc">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> Semantic Labeling Processor}
  The following interpretations form a model of the rules.
  <xsl:apply-templates select="ceta:model"/>
  Then we obtain the set of labeled pairs
  <xsl:apply-templates select="ceta:dps/*"/>
  and the set of labeled rules        
  <xsl:apply-templates select="ceta:trs/*"/>
  \bigskip
  <xsl:apply-templates select="*[4]">
    <xsl:with-param name="indent" select="concat($indent, '.1')"/>
  </xsl:apply-templates>
</xsl:template>
    
<xsl:template mode="arithFun" match="ceta:natural">
  <xsl:apply-templates/>
</xsl:template>

<xsl:template mode="arithFun" match="ceta:variable">
  <xsl:text>x_{</xsl:text><xsl:apply-templates/><xsl:text>}</xsl:text>
</xsl:template>

<xsl:template mode="arithFun" match="ceta:sum">
 <xsl:for-each select="*">
   <xsl:apply-templates select="." mode="arithFun"/>
   <xsl:if test="position() != last()"><xsl:text>+</xsl:text></xsl:if>
 </xsl:for-each>
</xsl:template>

<xsl:template mode="arithFun" match="ceta:prod">
  <xsl:text>(</xsl:text>
  <xsl:for-each select="*">
    <xsl:apply-templates select="." mode="arithFun"/>
    <xsl:if test="position() != last()"><xsl:text>\cdot</xsl:text></xsl:if>
  </xsl:for-each>
  <xsl:text>)</xsl:text>        
</xsl:template>

<xsl:template mode="arithFun" match="ceta:minimum">
  <xsl:text>\min(</xsl:text>
  <xsl:for-each select="*">
    <xsl:apply-templates select="." mode="arithFun"/>
    <xsl:if test="position() != last()"><xsl:text>,</xsl:text></xsl:if>
  </xsl:for-each>
  <xsl:text>)</xsl:text>
</xsl:template>

<xsl:template mode="arithFun" match="ceta:maximum">
  <xsl:text>\max(</xsl:text>
  <xsl:for-each select="*">
    <xsl:apply-templates select="." mode="arithFun"/>
    <xsl:if test="position() != last()"><xsl:text>,</xsl:text></xsl:if>
  </xsl:for-each>
  <xsl:text>)</xsl:text>
</xsl:template>
    
<xsl:template match="ceta:model">
  <xsl:text>As carrier we take the set $</xsl:text>
  <xsl:choose>
    <xsl:when test="ceta:carrierSize/text() = 1"><xsl:text>\{0\}</xsl:text></xsl:when>
    <xsl:when test="ceta:carrierSize/text() = 2"><xsl:text>\{0,1\}</xsl:text></xsl:when>
    <xsl:when test="ceta:carrierSize/text() = 3"><xsl:text>\{0,1,2\}</xsl:text></xsl:when>
    <xsl:otherwise><xsl:text>\{0,\dots,</xsl:text><xsl:value-of select="ceta:carrierSize/text() - 1"/><xsl:text>\}</xsl:text></xsl:otherwise>
  </xsl:choose>
  <xsl:text>$.</xsl:text>
  Symbols are labeled by the interpretation of their arguments using the interpretations
  (modulo <xsl:value-of select="ceta:carrierSize/text()"/>):
  \begin{align*}
    <xsl:for-each select="ceta:interpret">
      <xsl:text>[</xsl:text><xsl:apply-templates select="ceta:name"/><xsl:text>]</xsl:text>
      <xsl:call-template name="genVars">
        <xsl:with-param name="n" select="ceta:arity"/>
      </xsl:call-template>
      <xsl:text> &amp;= </xsl:text>
      <xsl:apply-templates mode="arithFun" select="*[3]"/>\\
    </xsl:for-each>
    <xsl:text>[f](x_1,\dots,x_n) &amp;= 0</xsl:text>\\
      &amp;\text{for all other symbols f of arity n}\\
  \end{align*}
</xsl:template>
    
<xsl:template name="ceta:ProofStep">
  <xsl:param name="indent"/>
  <xsl:param name="name"/>
  <xsl:param name="justification"/>
  <xsl:param name="pairs"/>
  <xsl:param name="urules">null</xsl:param>
  <xsl:param name="rules">null</xsl:param>
  <xsl:param name="proof"/>
  Using the <xsl:value-of select="$name"/>
  <xsl:apply-templates select="$justification"/>
  <xsl:if test="string($urules) != 'null'">
    <xsl:choose>
      <xsl:when test="count($urules) &gt; 0">
        <xsl:text>together with the usable rule</xsl:text>
	<xsl:if test="count($urules) &gt; 1">s</xsl:if>
        <xsl:apply-templates select="$urules/.."/>
        <xsl:text>(w.r.t. the implicit argument filter of the reduction pair), </xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>having no usable rules (w.r.t. the implicit argument filter of the
        reduction pair), </xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:if>
  <xsl:choose>
    <xsl:when test="count($pairs) &gt; 0">
      <xsl:text>the pair</xsl:text>
      <xsl:if test="count($pairs) &gt; 1">s</xsl:if> 
      <xsl:apply-templates select="$pairs/.."/>
      <xsl:if test="string($rules) != 'null'">
        <xsl:text> and </xsl:text>
        <xsl:choose>
          <xsl:when test="count($rules) &gt; 0">
            <xsl:text>the rule</xsl:text>
	    <xsl:if test="count($rules) &gt; 1">s</xsl:if>
            <xsl:apply-templates select="$rules/.."/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>no rules</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:if>
      remain<xsl:if test="count($pairs) = 1 and string($rules) = 'null'">s</xsl:if>.
    </xsl:when>
    <xsl:otherwise>
      <xsl:choose>
        <xsl:when test="string($rules) != 'null' and count($rules) &gt; 0">
          <xsl:text>all pairs could be removed, but the rule</xsl:text>
	  <xsl:if test="count($rules) &gt; 1">s</xsl:if>
          <xsl:apply-templates select="$rules/.."/>
          remain<xsl:if test="count($rules) &gt; 1">s</xsl:if>.
        </xsl:when>
        <xsl:when test="string($rules) != 'null'">
          <xsl:text>all pairs and rules could be removed.</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>all pairs could be removed.</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:otherwise>
  </xsl:choose>
  <xsl:if test="count($pairs) &gt; 0">
  \bigskip
  <xsl:apply-templates select="$proof">
    <xsl:with-param name="indent" select="concat($indent,'.1')"/>
  </xsl:apply-templates>
  </xsl:if>
</xsl:template>
    
<xsl:template match="ceta:simpleProjection">
  <xsl:choose>
    <xsl:when test="count(ceta:projEntry) &gt; 1">
      \begin{align*}
      <xsl:for-each select="ceta:projEntry">
        \pi(<xsl:apply-templates select="ceta:name"/>)
        &amp;=
        <xsl:value-of select="ceta:argument"/>
	\\
      </xsl:for-each>
      \end{align*}
    </xsl:when>
    <xsl:otherwise>
      <xsl:text> $\pi(</xsl:text>
      <xsl:apply-templates select="ceta:projEntry/ceta:name"/>
      <xsl:text>) = </xsl:text>
      <xsl:value-of select="ceta:projEntry/ceta:argument"/>
      <xsl:text>$, </xsl:text>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>
    
<xsl:template match="ceta:spscProc">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> Subterm Criterion Processor}
  <xsl:call-template name="ceta:ProofStep">
    <xsl:with-param name="indent" select="$indent"/>
    <xsl:with-param name="name">simple projection</xsl:with-param>
    <xsl:with-param name="justification" select="ceta:simpleProjection"/>
    <xsl:with-param name="pairs" select="ceta:dps/ceta:rules/*"/>
    <xsl:with-param name="proof" select="*[3]"/>
  </xsl:call-template>
</xsl:template>

<xsl:template match="ceta:redPairProc">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> Reduction Pair Processor}
  <xsl:call-template name="ceta:ProofStep">
    <xsl:with-param name="indent" select="$indent"/>
    <xsl:with-param name="justification" select="ceta:redPair"/>
    <xsl:with-param name="pairs" select="ceta:dps/ceta:rules/*"/>
    <xsl:with-param name="proof" select="*[3]"/>
  </xsl:call-template>
</xsl:template>

<xsl:template match="ceta:redPairUrProc">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> Reduction Pair Processor with Usable Rules}
  <xsl:call-template name="ceta:ProofStep">
    <xsl:with-param name="indent" select="$indent"/>
    <xsl:with-param name="justification" select="ceta:redPair"/>
    <xsl:with-param name="pairs" select="ceta:dps/ceta:rules/*"/>
    <xsl:with-param name="urules" select="ceta:usableRules/ceta:rules/*"/>
    <xsl:with-param name="proof" select="*[4]"/>
  </xsl:call-template>
</xsl:template>
        
<xsl:template match="ceta:monoRedPairProc">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> Monotonic Reduction Pair Processor}
  <xsl:call-template name="ceta:ProofStep">
    <xsl:with-param name="indent" select="$indent"/>
    <xsl:with-param name="justification" select="ceta:redPair"/>
    <xsl:with-param name="pairs" select="ceta:dps/ceta:rules/*"/>
    <xsl:with-param name="rules" select="ceta:trs/ceta:rules/*"/>
    <xsl:with-param name="proof" select="*[4]"/>
  </xsl:call-template>
</xsl:template>

<xsl:template match="ceta:monoRedPairUrProc">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> Monotonic Reduction Pair Processor with Usable Rules}
  <xsl:call-template name="ceta:ProofStep">
    <xsl:with-param name="indent" select="$indent"/>
    <xsl:with-param name="justification" select="ceta:redPair"/>
    <xsl:with-param name="pairs" select="ceta:dps/ceta:rules/*"/>
    <xsl:with-param name="urules" select="ceta:usableRules/ceta:rules/*"/>
    <xsl:with-param name="rules" select="ceta:trs/ceta:rules/*"/>
    <xsl:with-param name="proof" select="*[5]"/>
  </xsl:call-template>
</xsl:template>
    
<xsl:template match="ceta:pIsEmpty">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> P is empty}
  There are no pairs anymore.
</xsl:template>
    
<xsl:template match="ceta:ruleRemoval">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> Rule Removal Processor}
  <xsl:text>Using the</xsl:text>
  <xsl:apply-templates select="ceta:redPair"/>                
  <xsl:choose>
    <xsl:when test="count(ceta:trs/ceta:rules/*) &gt; 0">
      <xsl:text>the rule</xsl:text>
      <xsl:if test="count(ceta:trs/ceta:rules/*) &gt; 1">s</xsl:if> 
      <xsl:apply-templates select="ceta:trs/ceta:rules/*/.."/>
      remain<xsl:if test="count(ceta:trs/ceta:rules/*) = 1">s</xsl:if>.
      \bigskip
      <xsl:apply-templates select="*[3]">
        <xsl:with-param name="indent" select="concat($indent, '.1')"/>
      </xsl:apply-templates>
    </xsl:when>
    <xsl:otherwise>
      <xsl:text>all rules could be removed.</xsl:text>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>
    
<xsl:template match="ceta:rIsEmpty">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> R is empty}
  All rules have been removed.
</xsl:template>
    
<xsl:template match="ceta:depGraphProc">
  <xsl:param name="indent"/>
  \cetaHeading{<xsl:value-of select="$indent"/> Dependency Graph Processor}
  <xsl:variable name="all" select="count(ceta:component)"/>
  <xsl:variable name="real" select="count(ceta:component/*) - $all"/>
  <xsl:text>The dependency pairs are split into </xsl:text>
  <xsl:value-of select="$real"/>
  <xsl:text> component</xsl:text><xsl:if test="$real != 1">s</xsl:if>.
  <xsl:choose>
    <xsl:when test="$real &gt; 0">
      \begin{itemize}
      <xsl:apply-templates select="." mode="iterate">
        <xsl:with-param name="count" select="1"/>
        <xsl:with-param name="indent" select="$indent"/>
        <xsl:with-param name="index" select="1"/>
        <xsl:with-param name="n" select="$all"/>
      </xsl:apply-templates>
      \end{itemize}
    </xsl:when>
  </xsl:choose>        
</xsl:template>
    
<xsl:template mode="iterate" match="ceta:depGraphProc">
  <xsl:param name="indent"/>
  <xsl:param name="count"/>
  <xsl:param name="index"/>
  <xsl:param name="n"/>
  <xsl:variable name="newindex" select="$index + count(ceta:component[$count]/*) -1"/>
  <xsl:if test="$index != $newindex">
    <xsl:text>\item The </xsl:text>
    <xsl:choose>
      <xsl:when test="$index = 1">1\textsuperscript{st}</xsl:when>
      <xsl:when test="$index = 2">2\textsuperscript{nd}</xsl:when>
      <xsl:when test="$index = 3">3\textsuperscript{rd}</xsl:when>
      <xsl:otherwise><xsl:value-of select="$index"/>\textsuperscript{th}</xsl:otherwise>
    </xsl:choose>
    <xsl:text> component contains the pair</xsl:text>
    <xsl:if test="count(ceta:component[$count]/ceta:dps/ceta:rules/ceta:rule) &gt; 1">s</xsl:if>
    <xsl:apply-templates select="ceta:component[$count]/ceta:dps/*"/>
    \medskip
    <xsl:apply-templates select="ceta:component[$count]/*[2]">
      <xsl:with-param name="indent" select="concat($indent, '.', $index)"/>   
    </xsl:apply-templates>
  </xsl:if>
  <xsl:if test="$count &lt; $n">
    <xsl:apply-templates select="." mode="iterate">
      <xsl:with-param name="indent" select="$indent"/>
      <xsl:with-param name="count" select="$count + 1"/>
      <xsl:with-param name="index" select="$newindex"/>
      <xsl:with-param name="n" select="$n"/>
    </xsl:apply-templates>
  </xsl:if>        
</xsl:template>
    
<xsl:template name="var" match="ceta:var">
  <xsl:text>\var{</xsl:text><xsl:value-of select="translate(.,'_','-')"/><xsl:text>}</xsl:text>
</xsl:template>
    
<xsl:template match="ceta:name">
  <xsl:choose>
    <xsl:when test="@sharp = 'true'">
      <xsl:text>\dpFun{</xsl:text><xsl:value-of select="translate(text(),'_','-')"/><xsl:text>}^{\sharp}</xsl:text>
    </xsl:when>
    <xsl:otherwise>
      <xsl:text>\fun{</xsl:text><xsl:value-of select="translate(text(),'_','-')"/><xsl:text>}</xsl:text>
    </xsl:otherwise>
  </xsl:choose>
  <xsl:if test="count(ceta:label) &gt; 0">
  <xsl:text>_{\lab{</xsl:text>
    <xsl:for-each select="ceta:label">
      <xsl:if test="count(ceta:natural) != 1"><xsl:text>(</xsl:text></xsl:if>
      <xsl:for-each select="ceta:natural">
        <xsl:apply-templates/>
        <xsl:if test="position() != last()">,</xsl:if>                    
      </xsl:for-each>
      <xsl:if test="count(ceta:natural) != 1"><xsl:text>)</xsl:text></xsl:if>
      <xsl:if test="position() != last()">,</xsl:if>
    </xsl:for-each>     
  <xsl:text>}}</xsl:text>
  </xsl:if>
</xsl:template>
    
<xsl:template match="ceta:funapp">
  <xsl:apply-templates select="ceta:name"/>
  <xsl:if test="count(ceta:arg) &gt; 0">
  <xsl:text>(</xsl:text>
  <xsl:for-each select="ceta:arg">
    <xsl:apply-templates/>
    <xsl:if test="position() != last()"><xsl:text>,</xsl:text></xsl:if>
  </xsl:for-each>
  <xsl:text>)</xsl:text>
  </xsl:if>
</xsl:template>
    
<xsl:template match="ceta:box">
  <xsl:text>\Box</xsl:text>
</xsl:template>
    
<xsl:template match="ceta:funContext">
  <xsl:apply-templates select="ceta:name"/>
  <xsl:text>(</xsl:text>
  <xsl:for-each select="ceta:before/*">
    <xsl:apply-templates select="."/><xsl:text>,</xsl:text>
  </xsl:for-each>
  <xsl:apply-templates select="*[3]"/>
  <xsl:for-each select="ceta:after/*">
    <xsl:text>,</xsl:text><xsl:apply-templates select="."/>
  </xsl:for-each>
  <xsl:text>)</xsl:text>
</xsl:template>
    
<xsl:template match="ceta:rules">
  <xsl:choose>
    <xsl:when test="count(ceta:rule) = 0"/>
    <xsl:when test="count(ceta:rule) = 1">
      <xsl:text> $</xsl:text>
      <xsl:apply-templates select="ceta:rule/ceta:lhs"/>
      <xsl:text>\to</xsl:text>
      <xsl:apply-templates select="ceta:rule/ceta:rhs"/>
      <xsl:text>$ </xsl:text>
    </xsl:when>
    <xsl:otherwise>
    <xsl:text>\begin{align*}</xsl:text>
      <xsl:for-each select="ceta:rule">
        <xsl:text/>
        <xsl:apply-templates select="ceta:lhs"/>
        <xsl:text>&amp;\to</xsl:text>
        <xsl:apply-templates select="ceta:rhs"/>
	<xsl:text>\\</xsl:text>
      </xsl:for-each>
    \end{align*}
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>
    
<xsl:template match="ceta:substitution">
  <xsl:choose>
    <xsl:when test="count(ceta:substEntry) = 0"><xsl:text>\varnothing</xsl:text></xsl:when>
    <xsl:otherwise>    
      <xsl:text>\{</xsl:text>
      <xsl:for-each select="ceta:substEntry">
        <xsl:apply-templates select="*[1]"/>/<xsl:apply-templates select="*[2]"/>
        <xsl:if test="last() != position()">, </xsl:if>
      </xsl:for-each>
      <xsl:text>\}</xsl:text>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>

<xsl:template match="ceta:open">
  \bigskip
  
  {\Large\bf Unfinished Proof!}
</xsl:template>
    
</xsl:stylesheet>
