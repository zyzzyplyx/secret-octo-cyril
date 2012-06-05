package util.propnet.architecture.components;

import util.propnet.architecture.Component;

/**
 * The Transition class is designed to represent pass-through gates.
 */
@SuppressWarnings("serial")
public final class Transition extends Component
{
	/**
	 * Returns the value of the input to the transition.
	 * 
	 * @see util.propnet.architecture.Component#getValue()
	 */
	@Override
	public boolean getValue()
	{
		return getSingleInput().getValue();
	}

	/**
	 * @see util.propnet.architecture.Component#toString()
	 */
	@Override
	public String toString()
	{
		return "TRANS @"+this.bitIndex;
		//return toDot("box", "grey", "TRANSITION");
	}

	@Override
	public String getCompileString() {
		return this.getSingleInput().getCompileString(); //TRANS from: "+this.getSingleInput().toString();
	}

	@Override
	public String getEvalExp() {
		return "b["+bitIndex+"]="+getCompileString()+";";
	}
}