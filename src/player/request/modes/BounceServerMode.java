package player.request.modes;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;

public class BounceServerMode extends PlayerServerMode {

	private Socket socket = null;
	private PrintWriter writer;
	private BufferedReader reader;
	
	public BounceServerMode(Socket socket) throws IOException {
		this.socket = socket;
		this.writer = new PrintWriter(socket.getOutputStream());
		this.reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
	}
	
	@Override
	public String getRequest() throws IOException {
		String result = reader.readLine();
		return result;
	}

	@Override
	public void sendResponse(String response) throws IOException {
		if (!response.endsWith("\n")) response += "\n";
		writer.write(response);
		writer.flush();
	}

	@Override
	public void tearDown() throws IOException {
		writer.close();
		reader.close();
		socket.close();
	}

	@Override
	public String getHostAddress() {
		return null;
	}

	@Override
	public int getPort() {
		return -1;
	}

}
