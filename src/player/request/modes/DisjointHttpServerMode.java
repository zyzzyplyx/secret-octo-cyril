package player.request.modes;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

import util.http.HttpReader;
import util.http.HttpWriter;

public class DisjointHttpServerMode extends PlayerServerMode {

	private ServerSocket listener;
	private Socket connection = null;
	
	public DisjointHttpServerMode(ServerSocket serverSocket) {
		this.listener = serverSocket;
	}
	
	@Override
	public String getRequest() throws IOException {
		connection = listener.accept();
		String in = HttpReader.readAsServer(connection);
		if (in.length() == 0) {
		    throw new IOException("Empty message received.");
		}
		return in;
	}

	@Override
	public void sendResponse(String response) throws IOException {
		HttpWriter.writeAsServer(connection, response);
		connection.close();
		connection = null;
	}

	@Override
	public void tearDown() {
		if (listener != null) {
			try {
				listener.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	@Override
	public String getHostAddress() {
		return this.listener.getInetAddress().getHostAddress();
	}

	@Override
	public int getPort() {
		return this.listener.getLocalPort();
	}

}
