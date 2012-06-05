package util.propnet.architecture.components;

import util.propnet.architecture.Component;

/**
 * The And class is designed to represent logical AND gates.
 */
@SuppressWarnings("serial")
public final class And extends Component
{
	/**
	 * Returns true if and only if every input to the and is true.
	 * 
	 * @see util.propnet.architecture.Component#getValue()
	 */
	@Override
	public boolean getValue()
	{
		for ( Component component : getInputs() )
		{
			if ( !component.getValue() )
			{
				return false;
			}
		}
		return true;
	}

	/**
	 * @see util.propnet.architecture.Component#toString()
	 */
	@Override
	public String toString()
	{
		return "AND @"+this.bitIndex;
		//return toDot("invhouse", "grey", "AND");
	}

	@Override
	public String getCompileString() {
		String retStr = "(";//"b["+bitIndex+"] =";
		for(Component c : this.getInputs()){
			retStr += c.getCompileString()+"&&";
		}
		retStr = retStr.substring(0, retStr.length()-2) + ")"; // AND  "+this.getInputs().toString();
		return retStr;
	}

	@Override
	public String getEvalExp() {
		return "b["+bitIndex+"]="+getCompileString()+";";
	}

}
