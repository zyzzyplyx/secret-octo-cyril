package apps.server;

import java.io.IOException;
import java.net.Socket;
import java.net.URL;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import apps.server.registration.RegistrationServer;

import server.GameServer;
import util.configuration.ProjectConfiguration;
import util.game.CloudGameRepository;
import util.game.Game;
import util.game.GameRepository;
import util.game.LocalGameRepository;
import util.match.Match;
import util.networking.NetworkUtils;
import util.statemachine.Role;
import util.statemachine.exceptions.GoalDefinitionException;

public class ConsoleMatchServer {

	enum Mode {
		LIST_MODE,
		MATCH_MODE,
		HELP_MODE
	}
	
	private static CloudGameRepository cloudRepository;
	private static LocalGameRepository localRepository;
	
	private static int DEFAULT_START_CLOCK = 60;
	private static int DEFAULT_PLAY_CLOCK = 30;
	
	private static List<String> getParameters (String[] args, String flag) { 
		List<String> result = new ArrayList<String> ();
		
		boolean found = false;
		for (int i = 0; i < args.length; i++) {
			if (!found && args[i].equals(flag)) {
				found = true;
			} else if (found && args[i].charAt(0) != '-') {
				result.add(args[i]);
			} else if (found) {
				break;
			}
		}
		
		return result;
	}
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// Check directory structure and create if necessary
		if (!ProjectConfiguration.gameCacheDirectory.exists()) {
			ProjectConfiguration.gameCacheDirectory.mkdirs();
		}
		
		if (!ProjectConfiguration.gameLocalDirectory.exists()) {
			ProjectConfiguration.gameLocalDirectory.mkdirs();
		}
		
		// Setup repositories
		cloudRepository = new CloudGameRepository ("http://games.ggp.org/base/");
		localRepository = new LocalGameRepository ();
		
		// Decide mode
		Mode mode = Mode.MATCH_MODE;
		for (String s : args) {
			if (s.equals("-l")) mode = Mode.LIST_MODE;
			if (s.equals("-h")) mode = Mode.HELP_MODE;
		}
				
		switch (mode) {
		case MATCH_MODE:
			matchMode (args);
			break;
		case LIST_MODE:
			listMode (args);
			break;
		case HELP_MODE:
			helpMode (args);
			break;
		}

		System.exit(1);
	}

	private static void helpMode(String[] args) {
		System.out.println(
				  "-l   List available games. Use the string before the dash to reference the entry.\n"
				+ "-g   Specify the name of the game to player\n"
				+ "-p   List the player addresses with format <ip address>:<port number>.\n"
				+ "     These values may also be valid registration names if the -r flag is set.\n"
				+ "-n   List the player names in the same order as the addresses (optional)\n"
				+ "-s   Sets the start clock in seconds\n"
				+ "-t   Sets the play clock in seconds\n"
				+ "-r   Sets the registration server\n"
				+ "-h   Display this help message\n"
				);
	}
	
	private static Game findGame(String key) {
		Game result = null;
		
		if (result == null) result = cloudRepository.getGame(key);
		if (result == null) result = localRepository.getGame(key);
		
		return result;
	}

	private static void matchMode(String[] args) {
		
		// Load the game -- only play first game listed
		List<String> games = getParameters (args, "-g");
		if (games.size() == 0) {
			System.out.println("Expecting a game name after -g option, use -h for help");
			System.exit(1);
		}
		
		Game game = findGame (games.get(0));
		if (game == null) {
			System.out.println("Specified game could not be found");
			System.exit(1);
		}
		
		// Find the IP addresses and ports of players
		List<String> players = getParameters (args, "-p");
		List<String> hosts = new ArrayList<String> ();
		List<Integer> ports = new ArrayList<Integer> ();
		Map<String,URL> regPlayers = getRegisteredPlayers(args);

		// Make sure there are enough players for the roles in the game
		int numRoles = Role.computeRoles(game.getRules()).size();
		
		if (numRoles < 1) {
			System.out.println("Error with GDL -- zero roles found");
			System.exit(1);
		}
		
		if (numRoles > players.size()) {
			System.out.println(numRoles + " players needed but only " + players.size() + " specified.");
			System.exit(1);
		}
		
		while (players.size() > numRoles) {
			players.remove(players.size()-1);
		}
		
		// Parse addresses
		for (String address : players) {
			
			int colonIdx = address.indexOf(':');
			URL regPlayer = regPlayers.get(address);
			
			if (colonIdx == -1 && regPlayer == null) {
				System.out.println("Invalid player address: " + address);
				System.exit(1);
			}
			
			if (regPlayer == null) {
				String host = address.substring(0, colonIdx);
				hosts.add(host);
				
				try {
					Integer port = Integer.parseInt(address.substring(colonIdx + 1));
					ports.add(port);
				} catch (NumberFormatException e){
					System.out.println("Port number invalid for address: " + address);
					System.exit(1);
				}
			} else {
				hosts.add(regPlayer.getHost());
				ports.add(regPlayer.getPort());
			}
		}
		
		// Find player names -- generate default names if there are not enough names
		List<String> names = getParameters (args, "-n");
		while(names.size () < players.size()) {
			names.add("Player" + names.size());
		}
		
		int startClock = DEFAULT_START_CLOCK;
		int playClock = DEFAULT_PLAY_CLOCK;
		
		Integer cmdStartClock = getInteger(args, "-s");
		Integer cmdPlayClock = getInteger(args, "-t");
		
		if (cmdStartClock != null) startClock = cmdStartClock;
		if (cmdPlayClock != null) playClock = cmdPlayClock;
		
		String name = game.getName();
		if (name == null) name = games.get(0);
		
		// Remove spaces from matchid
		name = name.replaceAll(" ", "");
		
		Match match = new Match (name + "-" + Match.getRandomString(5), 
									startClock, playClock, game);
		
		GameServer server = new GameServer (match, hosts, ports, names);
		
		System.out.print("Beginning a match of " + name + 
				" with startclock of " + startClock + " and a playclock of " + playClock + " ...");
		server.run();
		System.out.println("done");
		
		try {
			List<Integer> goals = server.getGoals();
			
			for (int i = 0; i < goals.size(); i++) {
				System.out.println(names.get(i) + "(" + players.get(i) + "): " + goals.get(i));
			}
		} catch (GoalDefinitionException e) {
			System.out.println("Could not compute goals, check game description");
		}
	}

	private static Integer getInteger(String[] args, String flag) {
		List<String> strings = getParameters(args, flag);
		
		if(strings.size() < 1) return null;
		
		try {
			return Integer.parseInt(strings.get(0));
		} catch (NumberFormatException e) {
			return null;
		}
	}

	private static void printRepositoryContents (GameRepository repo) {
		for (String key : repo.getGameKeys()) {
			Game game = repo.getGame(key);
			
			if (game == null) continue;
			
			String actualName = game.getName();
			if (actualName == null) actualName = key;
			
			if (game != null) {
				System.out.println(key + " -- " 
						+ actualName + " -- " 
						+ Role.computeRoles(game.getRules()).size() + " players");
			}
		}
		
	}
	
	private static Map<String, URL> getRegisteredPlayers(String args[]) {
		List<String> regServersRaw = getParameters (args, "-r");
		Map<String,URL> players = new HashMap<String, URL>();
		if (regServersRaw.size() > 0) {
			try {
				Socket serverSocket = NetworkUtils.getSocketFromString(regServersRaw.get(0));
				players = RegistrationServer.queryList(serverSocket);
			} catch (UnknownHostException e) {
				System.out.println("Registration server could not be found");
			} catch (IOException e) {
				System.out.println("Failure connecting to registration server");
			}
			
		}
		return players;
	}
	
	// List the games in both repositories
	private static void listMode(String[] args) {
		
		System.out.println("---------- Games on ggp.org: ");
		printRepositoryContents(cloudRepository);
		System.out.println();
				
		System.out.println("---------- Local games:");
		printRepositoryContents(localRepository);
		System.out.println();
		
		List<String> regServersRaw = getParameters (args, "-r");
		if (regServersRaw.size() > 0) {
			System.out.println("--------- Players registered on " + regServersRaw.get(0));
			Map<String,URL> players = getRegisteredPlayers(args);
			if (players.size() > 0) {
				for (String name : players.keySet()) {
					System.out.println(name);
				}
			} else {
				System.out.println("--NONE--");
			}
		}
	}

}
