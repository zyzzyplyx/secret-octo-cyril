package player.request.modes;

import java.io.IOException;

public abstract class PlayerServerMode {

	public abstract String getRequest() throws IOException;
	
	public abstract void sendResponse(String response) throws IOException;
	
	public abstract void tearDown() throws IOException;
	
	public abstract String getHostAddress();

	public abstract int getPort();
}
