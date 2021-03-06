<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:param name="width" select="400"/>
<xsl:param name="height" select="400"/>
<xsl:template name="main" match="/">  <div>    <!-- Set Style -->    <style type="text/css" media="all">      
td.cell_normal {        width:  <xsl:value-of select="$width * 0.06"/>
px;        height: <xsl:value-of select="$height * 0.06"/>
px;        border: 2px solid #000;        background-color: #CCCCCC;      }      
td.cell_suicide {        width:  <xsl:value-of select="$width * 0.06"/>
px;        height: <xsl:value-of select="$height * 0.06"/>
px;        border: 2px solid #000;        background-color: #FFBBBB;      }      
table.board {        background-color: #000000;      }      img.piece {        width: <xsl:value-of select="$width * 0.9 * 0.06"/>
px;        height: <xsl:value-of select="$height * 0.9 * 0.06"/>
px;              }    </style>        <!-- Draw Board -->    <xsl:call-template name="board_normal">      <xsl:with-param name="cols" select="8"/>
      <xsl:with-param name="rows" select="6"/>
    </xsl:call-template>		      
    <xsl:call-template name="board_suicide">      <xsl:with-param name="cols" select="8"/>
      <xsl:with-param name="rows" select="6"/>
    </xsl:call-template>		
    
    </div>  </xsl:template><xsl:template name="cell_normal" match="state/fact">  <xsl:param name="row" select="1"/>
  <xsl:param name="col" select="1"/>
   <td class="cell_normal">  <xsl:attribute name="id">    <xsl:value-of select="'cell_'"/>
    <xsl:value-of select="$col"/>
    <xsl:value-of select="$row"/>
  </xsl:attribute>  <center>  <xsl:if test="//fact[relation='cell_normal' and argument[1]=$col and argument[2]=$row and argument[3]='red']"> <img class="piece" src="&ROOT;/resources/images/discs/red.png"/>
 </xsl:if>  <xsl:if test="//fact[relation='cell_normal' and argument[1]=$col and argument[2]=$row and argument[3]='black']"> <img class="piece" src="&ROOT;/resources/images/discs/black.png"/>
 </xsl:if>  </center>    </td>  </xsl:template><xsl:template name="board_normal_row">  <xsl:param name="cols" select="1"/>
  <xsl:param name="rows" select="1"/>
    <xsl:param name="row" select="1"/>
  <xsl:param name="col" select="1"/>
    <xsl:call-template name="cell_normal">    <xsl:with-param name="row" select="7 - $row"/>
    <xsl:with-param name="col" select="$col"/>
  </xsl:call-template>  <xsl:if test="$col &lt; $cols">    <xsl:call-template name="board_normal_row">      <xsl:with-param name="cols" select="$cols"/>
      <xsl:with-param name="rows" select="$rows"/>
      <xsl:with-param name="row" select="$row"/>
      <xsl:with-param name="col" select="$col + 1"/>
    </xsl:call-template>  </xsl:if></xsl:template><xsl:template name="board_normal_rows">  <xsl:param name="cols" select="1"/>
  <xsl:param name="rows" select="1"/>
    <xsl:param name="row" select="1"/>
  <tr>  <xsl:call-template name="board_normal_row">    <xsl:with-param name="cols" select="$cols"/>
    <xsl:with-param name="rows" select="$rows"/>
    <xsl:with-param name="row" select="$row"/>
  </xsl:call-template>  </tr>  <xsl:if test="$row &lt; $rows">    <xsl:call-template name="board_normal_rows">      <xsl:with-param name="cols" select="$cols"/>
      <xsl:with-param name="rows" select="$rows"/>
      <xsl:with-param name="row" select="$row + 1"/>
    </xsl:call-template>  </xsl:if></xsl:template><xsl:template name="board_normal">  <xsl:param name="cols" select="1"/>
  <xsl:param name="rows" select="1"/>
  <table class="board_normal">  <xsl:call-template name="board_normal_rows">    <xsl:with-param name="cols" select="$cols"/>
    <xsl:with-param name="rows" select="$rows"/>
  </xsl:call-template>  </table></xsl:template>
  
  <xsl:template name="cell_suicide" match="state/fact">  <xsl:param name="row" select="1"/>
  <xsl:param name="col" select="1"/>
   <td class="cell_suicide">  <xsl:attribute name="id">    <xsl:value-of select="'cell_'"/>
    <xsl:value-of select="$col"/>
    <xsl:value-of select="$row"/>
  </xsl:attribute>  <center>  <xsl:if test="//fact[relation='cell_suicide' and argument[1]=$col and argument[2]=$row and argument[3]='red']"> <img class="piece" src="&ROOT;/resources/images/discs/red.png"/>
 </xsl:if>  <xsl:if test="//fact[relation='cell_suicide' and argument[1]=$col and argument[2]=$row and argument[3]='black']"> <img class="piece" src="&ROOT;/resources/images/discs/black.png"/>
 </xsl:if>  </center>    </td>  </xsl:template><xsl:template name="board_suicide_row">  <xsl:param name="cols" select="1"/>
  <xsl:param name="rows" select="1"/>
    <xsl:param name="row" select="1"/>
  <xsl:param name="col" select="1"/>
    <xsl:call-template name="cell_suicide">    <xsl:with-param name="row" select="7 - $row"/>
    <xsl:with-param name="col" select="$col"/>
  </xsl:call-template>  <xsl:if test="$col &lt; $cols">    <xsl:call-template name="board_suicide_row">      <xsl:with-param name="cols" select="$cols"/>
      <xsl:with-param name="rows" select="$rows"/>
      <xsl:with-param name="row" select="$row"/>
      <xsl:with-param name="col" select="$col + 1"/>
    </xsl:call-template>  </xsl:if></xsl:template><xsl:template name="board_suicide_rows">  <xsl:param name="cols" select="1"/>
  <xsl:param name="rows" select="1"/>
    <xsl:param name="row" select="1"/>
  <tr>  <xsl:call-template name="board_suicide_row">    <xsl:with-param name="cols" select="$cols"/>
    <xsl:with-param name="rows" select="$rows"/>
    <xsl:with-param name="row" select="$row"/>
  </xsl:call-template>  </tr>  <xsl:if test="$row &lt; $rows">    <xsl:call-template name="board_suicide_rows">      <xsl:with-param name="cols" select="$cols"/>
      <xsl:with-param name="rows" select="$rows"/>
      <xsl:with-param name="row" select="$row + 1"/>
    </xsl:call-template>  </xsl:if></xsl:template><xsl:template name="board_suicide">  <xsl:param name="cols" select="1"/>
  <xsl:param name="rows" select="1"/>
  <table class="board_suicide">  <xsl:call-template name="board_suicide_rows">    <xsl:with-param name="cols" select="$cols"/>
    <xsl:with-param name="rows" select="$rows"/>
  </xsl:call-template>  </table></xsl:template>
  
  
  </xsl:stylesheet>



