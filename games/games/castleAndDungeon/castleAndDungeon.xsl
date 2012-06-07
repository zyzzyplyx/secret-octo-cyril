
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
<xsl:param name="width" select="500"/>
<xsl:param name="height" select="500"/>
<xsl:template name="main" match="/">  
  <div> <!-- Set Style -->    
  <style type="text/css" media="all"> 
    td.castle_cell {        width:  <xsl:value-of select="$width * 0.1"/>px; height: <xsl:value-of select="$height * 0.1"/>px;        border: 2px solid #000;        background-color: #CDB79E;        align: center;  valign: middle;    }      
    table.board_castle {   background-color: #000000;  }      img.piece {        width:   <xsl:value-of select="$width * 0.9 * 0.1"/>px;        height:   <xsl:value-of select="$height * 0.9 * 0.1"/>px;              }   
  td.dungeon_cell {        width:  <xsl:value-of select="$width * 0.1"/>px; height: <xsl:value-of select="$height * 0.1"/>px;        border: 2px solid #000;        background-color: #734A12;        align: center;  valign: middle;    }      
    </style>        
  <!-- Draw Board -->    
  <xsl:call-template   name="board_castle">      
    <xsl:with-param name="cols" select="4"/>   
    <xsl:with-param name="rows" select="4"/>   
  </xsl:call-template>     

  <xsl:call-template   name="board_dungeon">      
    <xsl:with-param name="cols" select="4"/>   
    <xsl:with-param name="rows" select="4"/>   
  </xsl:call-template>     
 </div>   
</xsl:template>
<xsl:template name="cell" match="state/fact"> 
  <xsl:param name="row" select="1"/>  <xsl:param name="col"   select="1"/> 
  <td class="castle_cell">  
  <xsl:attribute name="id">  
    <xsl:value-of select="'at_'"/>   
      <xsl:value-of   select="$row"/>   <xsl:value-of select="$col"/>   
  </xsl:attribute>    
  
  <xsl:choose>   
    <xsl:when test="//fact[relation='treasure' and argument[1]='castle' and argument[3]=$row and argument[4]=$col]"> 
      <xsl:attribute   name="style">background-color: #EEC900</xsl:attribute> 
    </xsl:when>   
  </xsl:choose>  

  <center>   

  <xsl:choose>   
    <xsl:when test="//fact[relation='at' and argument[1]='castle' and argument[2]='thief' and argument[3]='black' and argument[4]=$row and argument[5]=$col]">  
      <img class="piece"   src="&ROOT;/resources/images/chess/Black_Pawn.png"/> 
    </xsl:when>  
    <xsl:when test="//fact[relation='at' and argument[1]='castle' and argument[2]='guard' and argument[3]='black' and argument[4]=$row and argument[5]=$col]">  
      <img class="piece"   src="&ROOT;/resources/images/chess/Black_Knight.png"/> 
    </xsl:when>  
    <xsl:when test="//fact[relation='at' and argument[1]='castle' and argument[2]='wizard' and argument[3]='black' and argument[4]=$row and argument[5]=$col]">  
     <img class="piece"   src="&ROOT;/resources/images/chess/Black_Bishop.png"/> 
    </xsl:when>  
    <xsl:when test="//fact[relation='at' and argument[1]='castle' and argument[2]='thief' and argument[3]='white' and argument[4]=$row and argument[5]=$col]">  
      <img class="piece"   src="&ROOT;/resources/images/chess/White_Pawn.png"/> 
    </xsl:when>  
    <xsl:when test="//fact[relation='at' and argument[1]='castle' and argument[2]='guard' and argument[3]='white' and argument[4]=$row and argument[5]=$col]">  
      <img class="piece"   src="&ROOT;/resources/images/chess/White_Knight.png"/> 
    </xsl:when>  
    <xsl:when test="//fact[relation='at' and argument[1]='castle' and argument[2]='wizard' and argument[3]='white' and argument[4]=$row and argument[5]=$col]">  
     <img class="piece"   src="&ROOT;/resources/images/chess/White_Bishop.png"/> 
    </xsl:when>  
  </xsl:choose>
  

  </center>  
  </td>  
</xsl:template>
  
<xsl:template   name="board_castle_row">  
    <xsl:param name="cols" select="1"/>   <xsl:param name="rows" select="1"/>
    <xsl:param name="row"  select="1"/>  <xsl:param name="col" select="1"/>
    <xsl:call-template name="cell">    
      <xsl:with-param name="row" select="$row"/>  
      <xsl:with-param name="col" select="$col"/>   
    </xsl:call-template>  
    <xsl:if test="$col &lt; $cols">
      <xsl:call-template name="board_castle_row">     
        <xsl:with-param   name="cols" select="$cols"/>     
        <xsl:with-param name="rows"   select="$rows"/>  
        <xsl:with-param name="row"   select="$row"/> 
        <xsl:with-param name="col" select="$col + 1"/>  
      </xsl:call-template>  
    </xsl:if>
  </xsl:template>
  <xsl:template name="board_castle_rows">  
    <xsl:param name="cols" select="1"/>  <xsl:param name="rows"   select="1"/>  
    <xsl:param name="row" select="1"/>  
    <tr>   
      <xsl:call-template name="board_castle_row"> 
      <xsl:with-param   name="cols" select="$cols"/> 
      <xsl:with-param name="rows"   select="$rows"/>  
      <xsl:with-param name="row" select="$row"/>  
      </xsl:call-template>  
    </tr> 
    <xsl:if test="$row &lt; $rows"> 
      <xsl:call-template name="board_castle_rows">  
        <xsl:with-param   name="cols" select="$cols"/>   
        <xsl:with-param name="rows"   select="$rows"/>  
        <xsl:with-param name="row" select="$row + 1"/>   
      </xsl:call-template>  
     </xsl:if>
  </xsl:template>
  <xsl:template name="board_castle"> 
    <xsl:param name="cols" select="1"/>
    <xsl:param name="rows" select="1"/> 
    <table class="board_castle"> 
    <xsl:call-template   name="board_castle_rows">  
      <xsl:with-param name="cols"   select="$cols"/>  
      <xsl:with-param name="rows"   select="$rows"/> 
    </xsl:call-template> 
    </table>
  </xsl:template>

  <xsl:template name="at" match="state/fact"> 
  <xsl:param name="row" select="1"/>  <xsl:param name="col"   select="1"/> 
  <td class="dungeon_cell">  
  <xsl:attribute name="id">  
    <xsl:value-of select="'at_'"/>   
      <xsl:value-of   select="$row"/>   <xsl:value-of select="$col"/>   
  </xsl:attribute>    
  
  <xsl:choose>   
    <xsl:when test="//fact[relation='fireball' and argument[2]=$row and argument[3]=$col]"> 
      <xsl:attribute   name="style">background-color: #FF3300</xsl:attribute> 
    </xsl:when>   
    <xsl:when test="//fact[relation='treasure' and argument[1]='dungeon' and argument[3]=$row and argument[4]=$col]"> 
      <xsl:attribute   name="style">background-color: #EEC900</xsl:attribute> 
    </xsl:when>   
  </xsl:choose>  

  <center>   

  <xsl:choose>   
    <xsl:when test="//fact[relation='at' and argument[1]='dungeon' and argument[2]='thief' and argument[3]='black' and argument[4]=$row and argument[5]=$col]">  
      <img class="piece"   src="&ROOT;/resources/images/chess/Black_Pawn.png"/> 
    </xsl:when>  
    <xsl:when test="//fact[relation='at' and argument[1]='dungeon' and argument[2]='thief' and argument[3]='white' and argument[4]=$row and argument[5]=$col]">  
      <img class="piece"   src="&ROOT;/resources/images/chess/White_Pawn.png"/> 
    </xsl:when>  
    <xsl:when test="//fact[relation='at' and argument[1]='dungeon' and argument[2]='dragon' and argument[3]='black' and argument[4]=$row and argument[5]=$col]">  
      <img class="piece"   src="&ROOT;/resources/images/chess/Black_Queen.png"/> 
    </xsl:when>  
    <xsl:when test="//fact[relation='at' and argument[1]='dungeon' and argument[2]='dragon' and argument[3]='white' and argument[4]=$row and argument[5]=$col]">  
      <img class="piece"   src="&ROOT;/resources/images/chess/White_Queen.png"/> 
    </xsl:when>  
  </xsl:choose>
  

  </center>  
  </td>  
  </xsl:template>
  
  <xsl:template   name="board_dungeon_row">  
    <xsl:param name="cols" select="1"/>   <xsl:param name="rows" select="1"/>
    <xsl:param name="row"  select="1"/>  <xsl:param name="col" select="1"/>
    <xsl:call-template name="at">    
      <xsl:with-param name="row" select="$row"/>  
      <xsl:with-param name="col" select="$col"/>   
    </xsl:call-template>  
    <xsl:if test="$col &lt; $cols">
      <xsl:call-template name="board_dungeon_row">     
        <xsl:with-param   name="cols" select="$cols"/>     
        <xsl:with-param name="rows"   select="$rows"/>  
        <xsl:with-param name="row"   select="$row"/> 
        <xsl:with-param name="col" select="$col + 1"/>  
      </xsl:call-template>  
    </xsl:if>
  </xsl:template>
  <xsl:template name="board_dungeon_rows">  
    <xsl:param name="cols" select="1"/>  <xsl:param name="rows"   select="1"/>  
    <xsl:param name="row" select="1"/>  
    <tr>   
      <xsl:call-template name="board_dungeon_row"> 
      <xsl:with-param   name="cols" select="$cols"/> 
      <xsl:with-param name="rows"   select="$rows"/>  
      <xsl:with-param name="row" select="$row"/>  
      </xsl:call-template>  
    </tr> 
    <xsl:if test="$row &lt; $rows"> 
      <xsl:call-template name="board_dungeon_rows">  
        <xsl:with-param   name="cols" select="$cols"/>   
        <xsl:with-param name="rows"   select="$rows"/>  
        <xsl:with-param name="row" select="$row + 1"/>   
      </xsl:call-template>  
     </xsl:if>
  </xsl:template>
  <xsl:template name="board_dungeon"> 
    <xsl:param name="cols" select="1"/>
    <xsl:param name="rows" select="1"/> 
    <table class="board"> 
    <xsl:call-template   name="board_dungeon_rows">  
      <xsl:with-param name="cols"   select="$cols"/>  
      <xsl:with-param name="rows"   select="$rows"/> 
    </xsl:call-template> 
    </table>
  </xsl:template>
</xsl:stylesheet> 










