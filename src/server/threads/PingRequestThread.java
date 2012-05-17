package server.threads;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;

import player.request.grammar.PingRequest;

import server.request.RequestBuilder;
import util.http.HttpReader;
import util.http.HttpWriter;

public class PingRequestThread extends Thread {

	private final String host;
	private final int port;
	private final String playerName;
	public boolean result;
	public boolean connectionError;
	
	public PingRequestThread(String host, int port, 
			String playerName)
	{
		this.host = host;
		this.port = port;
		this.playerName = playerName;
		this.result = false;
	}

	
	@Override
	public void run()
	{
		try {
		    InetAddress theHost = InetAddress.getByName(host);
		    
			Socket socket = new Socket(theHost.getHostAddress(), port);
			String request = RequestBuilder.getPingRequest();
			
			HttpWriter.writeAsClient(socket, theHost.getHostName(), request, playerName);
			
			String response = HttpReader.readAsClient(socket, 1000);
			if (PingRequest.PING_SUCCESS.equals(response)) result = true;
		
			socket.close();
			
		} catch (IOException e) {
			connectionError = true;
		}

	}
}