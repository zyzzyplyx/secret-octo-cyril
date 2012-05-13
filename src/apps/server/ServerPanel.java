package apps.server;

import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.SocketException;
import java.net.URL;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.swing.AbstractAction;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JSeparator;
import javax.swing.JTabbedPane;
import javax.swing.JTextField;
import javax.swing.border.TitledBorder;

import player.GamePlayer;

import server.GameServer;
import util.game.Game;
import util.match.Match;
import util.networking.NetworkUtils;
import util.statemachine.Role;
import util.statemachine.StateMachine;
import util.statemachine.implementation.prover.ProverStateMachine;
import util.ui.GameSelector;
import util.ui.NativeUI;
import apps.server.error.ErrorPanel;
import apps.server.history.HistoryPanel;
import apps.server.publishing.PublishingPanel;
import apps.server.registration.RegistrationServer;
import apps.server.states.StatesPanel;
import apps.server.visualization.VisualizationPanel;

@SuppressWarnings("serial")
public final class ServerPanel extends JPanel 
	implements ActionListener, ItemListener
{    
	private static void createAndShowGUI(ServerPanel serverPanel)
	{
		JFrame frame = new JFrame("Game Server");
		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

		frame.setPreferredSize(new Dimension(1024, 768));
		frame.getContentPane().add(serverPanel);

		frame.pack();
		frame.setVisible(true);
	}

	public static void main(String[] args) throws SocketException, UnknownHostException
	{
	    NativeUI.setNativeUI();
	
		final ServerPanel serverPanel = new ServerPanel();
		javax.swing.SwingUtilities.invokeLater(new Runnable()
		{

			public void run()
			{
				createAndShowGUI(serverPanel);
			}
		});
	}
	
	private Game theGame;
	private final List<JTextField> hostportTextFields;
	private final JPanel managerPanel;
	private final JTabbedPane matchesTabbedPane;
	private final JTextField playClockTextField;
	private final JTextField regServerField;
	private final JPanel playersPanel;
	private final JTabbedPane leftHandSide;

	private final List<JTextField> playerNameTextFields;
	private final List<JLabel> roleLabels;
	private final JButton runButton;
	private final JButton refreshRegButton;
	
	private final JTextField startClockTextField;
	private final GameSelector gameSelector;
	
	private final InetAddress defaultPlayerIP;

	private final List<JComboBox> playerComboBoxes;
	private Map<String, URL> registeredPlayers;
	
	static private String manualConfigOption = "MANUAL_CONFIG";
	
	private JComboBox generatePlayerComboBox() {
		JComboBox result = new JComboBox();

		result.addItem(manualConfigOption);
		for (String name : registeredPlayers.keySet()) {
			result.addItem(name);
		}
		result.addItemListener(this);
		
		return result;
	}
	
	public ServerPanel() throws SocketException, UnknownHostException
	{
		super(new GridBagLayout());
		
		runButton = new JButton(runButtonMethod(this));
		refreshRegButton = new JButton(refreshRegButton(this));
		startClockTextField = new JTextField("30");
		playClockTextField = new JTextField("15");
		regServerField = new JTextField("");
		managerPanel = new JPanel(new GridBagLayout());
		matchesTabbedPane = new JTabbedPane();

		roleLabels = new ArrayList<JLabel>();
		hostportTextFields = new ArrayList<JTextField>();
		playerNameTextFields = new ArrayList<JTextField>();
		theGame = null;

		runButton.setEnabled(false);
		startClockTextField.setColumns(15);
		playClockTextField.setColumns(15);

		gameSelector = new GameSelector();
		
		playerComboBoxes = new ArrayList<JComboBox>();
		registeredPlayers = new HashMap<String, URL>();
		
		defaultPlayerIP = NetworkUtils.getALocalIPAddress();

		this.refreshRegServer();
		
		playersPanel = new JPanel(new GridBagLayout());
		
		int nRowCount = 0;
		managerPanel.setBorder(new TitledBorder("Manager"));
		managerPanel.add(new JLabel("Repository:"), new GridBagConstraints(0, nRowCount, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.NONE, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(gameSelector.getRepositoryList(), new GridBagConstraints(1, nRowCount++, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 5, 5));
        managerPanel.add(new JLabel("Game:"), new GridBagConstraints(0, nRowCount, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.NONE, new Insets(5, 5, 5, 5), 5, 5));
        managerPanel.add(gameSelector.getGameList(), new GridBagConstraints(1, nRowCount++, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 5, 5));
        managerPanel.add(new JSeparator(), new GridBagConstraints(0, nRowCount++, 2, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(new JLabel("Start Clock:"), new GridBagConstraints(0, nRowCount, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.NONE, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(startClockTextField, new GridBagConstraints(1, nRowCount++, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(new JLabel("Play Clock:"), new GridBagConstraints(0, nRowCount, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.NONE, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(playClockTextField, new GridBagConstraints(1, nRowCount++, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(new JSeparator(), new GridBagConstraints(0, nRowCount++, 2, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(new JLabel("Reg Server:"), new GridBagConstraints(0, nRowCount, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.NONE, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(regServerField, new GridBagConstraints(1, nRowCount++, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(refreshRegButton, new GridBagConstraints(1, nRowCount++, 2, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 0, 0));
		managerPanel.add(runButton, new GridBagConstraints(1, nRowCount, 1, 1, 0.0, 1.0, GridBagConstraints.SOUTH, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 0, 0));
		

		leftHandSide = new JTabbedPane();
		leftHandSide.addTab("Management", managerPanel);
		leftHandSide.addTab("Players", playersPanel);

		JPanel matchesPanel = new JPanel(new GridBagLayout());
		matchesPanel.setBorder(new TitledBorder("Matches"));
		matchesPanel.add(matchesTabbedPane, new GridBagConstraints(0, 0, 1, 1, 1.0, 1.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));

		this.add(leftHandSide, new GridBagConstraints(0, 0, 1, 1, 0.0, 1.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));
		this.add(matchesPanel, new GridBagConstraints(1, 0, 1, 1, 1.0, 1.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));

        gameSelector.getGameList().addActionListener(this);
        gameSelector.repopulateGameList();		
	}

	private AbstractAction refreshRegButton(final ServerPanel serverPanel) {
		return new AbstractAction("Refresh") {
			public void actionPerformed(ActionEvent evt) {
				serverPanel.refreshRegServer();
			}
		};
	}

	protected void refreshRegServer() {
		try {
			String addressString = this.regServerField.getText(); 
			Socket socket = NetworkUtils.getSocketFromString(addressString);
			if (socket == null) return;
			registeredPlayers = RegistrationServer.queryList(socket);
			socket.close();
		} catch (UnknownHostException e) {
			System.out.println("Error connecting to registration server: host unknown");
		} catch (IOException e) {
			System.out.println("Error connecting to registration server");
		}
		
		if (registeredPlayers.size() == 0) {
			System.out.println("No registered players found ...");
		}
		refreshPlayerPanel();
	}

	private AbstractAction runButtonMethod(final ServerPanel serverPanel)
	{
		return new AbstractAction("Run")
		{
			public void actionPerformed(ActionEvent evt)
			{
				try
				{
					String matchId = "BaseServer." + serverPanel.theGame.getKey() + "." + System.currentTimeMillis();
					
					int startClock = Integer.valueOf(serverPanel.startClockTextField.getText());
					int playClock = Integer.valueOf(serverPanel.playClockTextField.getText());
					Match match = new Match(matchId, startClock, playClock, serverPanel.theGame);

					List<String> hosts = new ArrayList<String>(serverPanel.hostportTextFields.size());
					List<Integer> ports = new ArrayList<Integer>(serverPanel.hostportTextFields.size());
					for (JTextField textField : serverPanel.hostportTextFields)
					{
	                    try {
	                        String[] splitAddress = textField.getText().split(":");
	                        String hostname = splitAddress[0];
	                        int port = Integer.parseInt(splitAddress[1]);
	                        
	                        hosts.add(hostname);
	                        ports.add(port);                    
	                    } catch(Exception ex) {
	                        ex.printStackTrace();
	                        return;
	                    } 					    
					}
					List<String> playerNames = new ArrayList<String>(serverPanel.playerNameTextFields.size());
					for (JTextField textField : serverPanel.playerNameTextFields)
					{
						playerNames.add(textField.getText());
					}

					HistoryPanel historyPanel = new HistoryPanel();
					ErrorPanel errorPanel = new ErrorPanel();
					VisualizationPanel visualizationPanel = new VisualizationPanel(theGame);
					StatesPanel statesPanel = new StatesPanel();

					JTabbedPane tab = new JTabbedPane();
					tab.addTab("History", historyPanel);
					tab.addTab("Error", errorPanel);
					tab.addTab("Visualization", visualizationPanel);
					tab.addTab("States", statesPanel);
					serverPanel.matchesTabbedPane.addTab(matchId, tab);
					serverPanel.matchesTabbedPane.setSelectedIndex(serverPanel.matchesTabbedPane.getTabCount()-1);
					
					GameServer gameServer = new GameServer(match, hosts, ports, playerNames);
					gameServer.addObserver(errorPanel);
					gameServer.addObserver(historyPanel);
					gameServer.addObserver(visualizationPanel);					
					gameServer.addObserver(statesPanel);
					gameServer.start();
					
					tab.addTab("Publishing", new PublishingPanel(gameServer));
				}
				catch (Exception e)
				{
					// Do nothing.
				}
			}
		};
	}
	
	protected void refreshPlayerPanel() {
		theGame = gameSelector.getSelectedGame();

        for (int i = 0; i < roleLabels.size(); i++)
        {
            playersPanel.remove(roleLabels.get(i));
            playersPanel.remove(hostportTextFields.get(i));
            playersPanel.remove(playerNameTextFields.get(i));
            playersPanel.remove(playerComboBoxes.get(i));
        }

        roleLabels.clear();
        hostportTextFields.clear();
        playerNameTextFields.clear();
        playerComboBoxes.clear();

        validate();
        runButton.setEnabled(false);
        if (theGame == null)
            return;            

        StateMachine stateMachine = new ProverStateMachine();
        stateMachine.initialize(theGame.getRules());
        List<Role> roles = stateMachine.getRoles();
        
        int newRowCount = 7;
        for (int i = 0; i < roles.size(); i++) {
            roleLabels.add(new JLabel(roles.get(i).getName().toString() + ":"));
            hostportTextFields.add(new JTextField(defaultPlayerIP.getHostAddress() + ":" +(GamePlayer.DEFAULT_PLAYER_PORT + i)));
            playerNameTextFields.add(new JTextField("defaultPlayerName"));
            playerComboBoxes.add(generatePlayerComboBox());
            
            hostportTextFields.get(i).setColumns(15);
            playerNameTextFields.get(i).setColumns(15);

            playersPanel.add(roleLabels.get(i), new GridBagConstraints(0, newRowCount, 1, 1, 1.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.NONE, new Insets(5, 5, 5, 5), 5, 5));
            playersPanel.add(playerComboBoxes.get(i), new GridBagConstraints(1, newRowCount++, 1, 1, 0.0, 0.0, GridBagConstraints.CENTER, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 5, 5));
            playersPanel.add(hostportTextFields.get(i), new GridBagConstraints(1, newRowCount++, 1, 1, 0.0, 0.0, GridBagConstraints.CENTER, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 5, 5));
            playersPanel.add(playerNameTextFields.get(i),  new GridBagConstraints(1, newRowCount++, 1, 1, 0.0, 0.0, GridBagConstraints.CENTER, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 5, 5));
            
        }
        managerPanel.add(runButton, new GridBagConstraints(1, newRowCount, 1, 1, 0.0, 1.0, GridBagConstraints.SOUTH, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 0, 0));

        validate();
        runButton.setEnabled(true);
	}

    @Override
    public void actionPerformed(ActionEvent e) {
        if (e.getSource() == gameSelector.getGameList()) {
            refreshPlayerPanel();
        }
    }

	@Override
	public void itemStateChanged(ItemEvent arg0) {
		for (int i = 0; i < playerComboBoxes.size(); i++) {
    		JComboBox comboBox = playerComboBoxes.get(i);
    		
    		if (arg0.getSource() == comboBox) {
    			String itemName = (String)arg0.getItem();
    			JTextField host = hostportTextFields.get(i);
    			JTextField playerName = playerNameTextFields.get(i);
    			if (itemName.equals(manualConfigOption)) {
    				host.setText("");
    				playerName.setText("");
    			} else {
	    			URL curURL = this.registeredPlayers.get(itemName);
	    			host.setText(curURL.getHost() + ":" + curURL.getPort());
	    			playerName.setText(itemName);
    			}
    		}
    	}
	}
}
