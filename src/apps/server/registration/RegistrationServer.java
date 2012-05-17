package apps.server.registration;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.MalformedURLException;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.URL;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import server.threads.PingRequestThread;
import util.http.HttpReader;
import util.http.HttpWriter;
import util.networking.NetworkUtils;


import external.JSON.JSONException;
import external.JSON.JSONObject;


public class RegistrationServer {

	public static final String DEFAULT_REG_IP = "10.31.1.100";

	private static final String FAILURE_MSG = "failure";

	public static int DEFAULT_REG_PORT = 9117;
	
	public static String REGISTRATION_CMD = "register";
	public static String BOUNCE_CMD = "bounce";
	public static String SUCCESS_RESP = "success";
	public static String INACCESSIBLE_RESP = "inaccessible";
	public static String LIST_CMD = "list";
	
	private static Random rand = new Random();

	class Forward extends Thread {
		public final Socket playerSide;
		public final ServerSocket exposedSide;
		public final PrintWriter playerWriter;
		public final BufferedReader playerReader;
		
		public Forward(Socket playerSide, BufferedReader in, PrintWriter out) throws IOException {
			this.exposedSide = generateServerSocket();
			this.playerSide = playerSide;
			this.playerReader = in;
			this.playerWriter = out;
		}
		
		private ServerSocket generateServerSocket() throws IOException {
			InetAddress inetAddress = NetworkUtils.getALocalIPAddress();
			ServerSocket result = new ServerSocket(0, 0, inetAddress);
			return result;
		}
		
		public void tearDown() throws IOException {
			if (playerSide != null) {
				this.playerReader.close();
				this.playerWriter.close();
				playerSide.close();
			}
			
			if (exposedSide != null) {
				exposedSide.close();
			}
		}
		
		/**
		 * Pipe connections to and from the player
		 */
		@Override 
		public void run() {
			while (!interrupted()) {
				try {
					Socket connection = exposedSide.accept();
					String in = HttpReader.readAsServer(connection);
					if (!in.endsWith("\n")) in += "\n";
					this.playerWriter.write(in);
					this.playerWriter.flush();
					String out = this.playerReader.readLine();
					if (out != null) HttpWriter.writeAsServer(connection, out);
					connection.close();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
			try {
				tearDown();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	};
	
	HashMap<String, URL> registrations = new HashMap<String, URL>();
	HashMap<String, Forward> forwards = new HashMap<String, Forward>();
	int serverPort;
	
	public RegistrationServer() {
		this(DEFAULT_REG_PORT);
	}
	
	public RegistrationServer(int port) {
		this.serverPort = port;
	}
	
	static public void main(String argv[]) throws IOException {
		InetAddress address = NetworkUtils.getALocalIPAddress();
		ServerSocket socket = new ServerSocket(DEFAULT_REG_PORT, 0, address);
		
		RegistrationServer regServer = new RegistrationServer();
		System.out.println("Registration server started on " + 
				socket.getInetAddress().getHostAddress() + ":"
				+ socket.getLocalPort());
		
		while (true) {
			Socket newConnection = socket.accept();
			BufferedReader in;
			in = new BufferedReader(new InputStreamReader(newConnection.getInputStream()));
			PrintWriter out = new PrintWriter(newConnection.getOutputStream(), true);
			
			String message = in.readLine();
			if (message == null) {
				in.close();
				newConnection.close();
				continue;
			}
			String[] tokens = message.split("\\s+");
			
			boolean keepAlive = false;
			if (tokens.length > 0) {
				String command = tokens[0].toLowerCase();
				String response = FAILURE_MSG + "\n";
				
				if (command.equals(REGISTRATION_CMD) && tokens.length > 2) {
					String name = tokens[1];
					String host = null;
					int registrationPort = -1;
					if (tokens.length > 3) {
						host = tokens[2];
						registrationPort = Integer.parseInt(tokens[3]);
					}
					if (host != null) {
						boolean accessible = verifyPlayerAccessible(name, host, registrationPort);
						if (accessible) {
							regServer.register(name, host, registrationPort);
							response = SUCCESS_RESP + "\n";
						} else {
							response = INACCESSIBLE_RESP;
						}
					} else {
						regServer.clearRegistration(name);
						response = "clear\n";
					}
				} else if (command.equals(BOUNCE_CMD) && tokens.length > 1) {
					String name = tokens[1];
					Forward newForward = regServer.new Forward(newConnection, in, out);
					ServerSocket newSocket = newForward.exposedSide;
					String host = newSocket.getInetAddress().getHostAddress();
					regServer.register(name, host, newSocket.getLocalPort());
					newForward.start();
					keepAlive = true;
					response = SUCCESS_RESP + "\n";
				} else if (command.equals(LIST_CMD)) {
					// Randomly verify that a player in the list is still alive
					regServer.randomVerify();
					
					response = regServer.list();
				}
				
				out.write(response);
				out.flush();
			}
			
			if (!keepAlive) {
				in.close();
				out.close();
				newConnection.close();				
			}
		}
	}
	
	private void randomVerify() {
		List<String> allKeys =new ArrayList<String>(registrations.keySet());
		int randInt = rand.nextInt(allKeys.size());
		String name = allKeys.get(randInt);
		URL url = registrations.get(name);
		if (!verifyPlayerAccessible(name, url.getHost(), url.getPort())) {
			registrations.remove(name);
		}
	}

	private String list() {
		JSONObject jobject = new JSONObject(registrations);
		return jobject.toString() + "\n";
	}

	private void register(String name, String host, int registrationPort) throws MalformedURLException {
		URL url = new URL("http", host, registrationPort, "");
		registrations.put(name, url);
		
		displayRegistrations(registrations);	
	}
	
	public void clearRegistration(String name) {
		this.registrations.remove(name);
		Forward forward = this.forwards.remove(name);
		if (forward != null) {
			forward.interrupt();
		}
		displayRegistrations(registrations);
	}

	private static boolean verifyPlayerAccessible(String name, String host, int playerPort) {
		// Attempt to ping the player at the given URL
		PingRequestThread pingThread = 
				new PingRequestThread(host, playerPort, name);
		try {
			pingThread.start();
		} catch (Exception e) { }
		try {
			Thread.sleep(1000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		pingThread.interrupt();
		return pingThread.result && !pingThread.connectionError;
	}

	static private void displayRegistrations(Map<String,URL> registrations) {
		System.out.println();
		System.out.println("Current Registrations: ");
		if (registrations.size() > 0) {
			for (String name : registrations.keySet()) {
				System.out.println("  " + name + ": " + registrations.get(name).toString());
			}
		} else {
			System.out.println("-- NONE --");
		}
	}

	static public String 
	sendRegistration (Socket serverSocket, String playerName, String address, int port) 
			throws IOException {
		
		playerName = playerName.replace(" ", "");
		
		String message = REGISTRATION_CMD + " " + playerName + " " + address + " " + port + "\n";
		PrintWriter out = new PrintWriter(serverSocket.getOutputStream(), true);
		out.write(message);
		out.flush();
		
		BufferedReader in;
		in = new BufferedReader(new InputStreamReader(serverSocket.getInputStream()));
		String response = in.readLine();
		
		return response;

	}
	
	static public boolean
	sendBounceRegistration(Socket serverSocket, String playerName) throws IOException {
		String message = BOUNCE_CMD + " " + playerName + "\n";
		PrintWriter out = new PrintWriter(serverSocket.getOutputStream(), true);
		out.write(message);
		out.flush();
		
		BufferedReader in;
		in = new BufferedReader(new InputStreamReader(serverSocket.getInputStream()));
		String response = in.readLine();
		
		return SUCCESS_RESP.equals(response);
	}
	
	static public Map<String, URL>
	queryList() throws UnknownHostException, IOException {
		Socket server = new Socket(DEFAULT_REG_IP, DEFAULT_REG_PORT);
		return queryList(server);
	}
	
	static public Map<String, URL> 
	queryList(Socket server) throws IOException {
		
		String message = LIST_CMD + "\n";
		PrintWriter out = new PrintWriter(server.getOutputStream(), true);
		out.write(message);
		out.flush();
		
		BufferedReader in;
		in = new BufferedReader(new InputStreamReader(server.getInputStream()));
		String response = in.readLine();
		
		// Convert JSON back into map of URLs
		HashMap<String, URL> result = new HashMap<String, URL>();
		if (response != null) {
			try {
				JSONObject jobject = new JSONObject(response);
				if (jobject != null && jobject.length() > 0) {
					for (String name : JSONObject.getNames(jobject)) {
						String addressString = jobject.getString(name);
						URL address = new URL(addressString);
						result.put(name, address);
					}
				}
			} catch (JSONException e) {
				e.printStackTrace();
			}
		}
		
		out.close();
		in.close();
		
		return result;
	}
}
