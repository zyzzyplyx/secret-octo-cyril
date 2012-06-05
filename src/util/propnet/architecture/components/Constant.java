package util.propnet.architecture.components;

import util.propnet.architecture.Component;

/**
 * The Constant class is designed to represent nodes with fixed logical values.
 */
@SuppressWarnings("serial")
public final class Constant extends Component
{
	/** The value of the constant. */
	private final boolean value;

	/**
	 * Creates a new Constant with value <tt>value</tt>.
	 * 
	 * @param value
	 *            The value of the Constant.
	 */
	public Constant(boolean value)
	{
		this.value = value;
	}

	/**
	 * Returns the value that the constant was initialized to.
	 * 
	 * @see util.propnet.architecture.Component#getValue()
	 */
	@Override
	public boolean getValue()
	{
		return value;
	}

	/**
	 * @see util.propnet.architecture.Component#toString()
	 */
	@Override
	public String toString()
	{
		return Boolean.toString(value).toUpperCase() + " @"+this.bitIndex;
		//return toDot("doublecircle", "grey", Boolean.toString(value).toUpperCase());
	}

	@Override
	public String getCompileString() {
		return (value? "true":"false");//"+value;
	}

	@Override
	public String getEvalExp() {
		return "b["+bitIndex+"]="+getCompileString()+";";
	}
}