package apps.player;

import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;
import java.io.IOException;
import java.net.InetAddress;
import java.net.SocketException;
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
import javax.swing.JTabbedPane;
import javax.swing.JTextField;
import javax.swing.border.TitledBorder;

import player.GamePlayer;
import player.gamer.SingleGameGamer;
import util.networking.NetworkUtils;
import util.reflection.ProjectSearcher;
import util.ui.NativeUI;
import apps.player.config.ConfigPanel;
import apps.player.detail.DetailPanel;
import apps.player.match.MatchPanel;
import apps.player.network.NetworkPanel;

@SuppressWarnings("serial")
public final class PlayerPanel extends JPanel implements WindowListener, MouseListener
{
	private static void createAndShowGUI(PlayerPanel playerPanel)
	{
		JFrame frame = new JFrame("Game Player");
		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

		frame.setPreferredSize(new Dimension(1024, 768));
		frame.getContentPane().add(playerPanel);
		frame.addWindowListener(playerPanel);

		frame.pack();
		frame.setVisible(true);
	}

	public static void main(String[] args) throws IOException
	{
	    NativeUI.setNativeUI();	    

	    final PlayerPanel playerPanel = new PlayerPanel();
	    javax.swing.SwingUtilities.invokeLater(new Runnable()
	    {

		public void run()
		{
		    createAndShowGUI(playerPanel);
		}
	    });
	}

	private final JButton createButton;
	private final JButton abortButton;
	private final Map<JTabbedPane, GamePlayer> playerMap = new HashMap<JTabbedPane, GamePlayer>();
	private final JTabbedPane playersTabbedPane;

	private final JTextField portTextField;
	private final JTextField regServerField;
	private final JComboBox ipComboBox;

	private final JComboBox typeComboBox;
	
	private JTabbedPane currentPane = null;
	
	private Integer defaultPort = 9147;
	
	private List<Class<?>> gamers = ProjectSearcher.getAllClassesThatAre(SingleGameGamer.class);

	public PlayerPanel() throws SocketException, UnknownHostException
	{
		super(new GridBagLayout());

		portTextField = new JTextField(defaultPort.toString());
		regServerField = new JTextField();
		typeComboBox = new JComboBox();
		ipComboBox = new JComboBox();
		createButton = new JButton(createButtonMethod(this));
		abortButton = new JButton(abortButtonMethod(this));
		playersTabbedPane = new JTabbedPane();
		playersTabbedPane.addMouseListener(this);

		portTextField.setColumns(15);

		// Add the gamers
		List<Class<?>> gamersCopy = new ArrayList<Class<?>>(gamers);
		for(Class<?> gamer : gamersCopy)
		{
			SingleGameGamer g;
			try {
				g = (SingleGameGamer) gamer.newInstance();
				typeComboBox.addItem(g.getName());
			} catch(Exception ex) {
			    gamers.remove(gamer);
			}
		}
		
		// Add the available IP addresses
		for (InetAddress address : NetworkUtils.getLocalIPList()) {
			ipComboBox.addItem(address.getHostAddress());
		}

		JPanel managerPanel = new JPanel(new GridBagLayout());
		
		managerPanel.setBorder(new TitledBorder("Manager"));

		managerPanel.add(new JLabel("Port:"), new GridBagConstraints(0, 0, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.NONE, new Insets(20, 5, 5, 5), 5, 5));
		managerPanel.add(portTextField, new GridBagConstraints(1, 0, 1, 1, 1.0, 0.0, GridBagConstraints.CENTER, GridBagConstraints.HORIZONTAL, new Insets(20, 5, 5, 5), 5, 5));
		managerPanel.add(new JLabel("Type:"), new GridBagConstraints(0, 1, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.NONE, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(typeComboBox, new GridBagConstraints(1, 1, 1, 1, 1.0, 0.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(new JLabel("Reg Server:"), new GridBagConstraints(0, 2, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.NONE, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(regServerField, new GridBagConstraints(1, 2, 1, 1, 1.0, 0.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(new JLabel("IP Address:"), new GridBagConstraints(0, 3, 1, 1, 0.0f, 0.0, GridBagConstraints.EAST, GridBagConstraints.NONE, new Insets(5, 5, 5,5), 5, 5));
		managerPanel.add(ipComboBox, new GridBagConstraints(1, 3, 1, 1, 1.0, 0.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));
		managerPanel.add(createButton, new GridBagConstraints(1, 4, 1, 1, 1.0, 1.0, GridBagConstraints.SOUTH, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 40, 5), 0, 0));
		managerPanel.add(abortButton, new GridBagConstraints(1, 4, 1, 1, 1.0, 1.0, GridBagConstraints.SOUTH, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 0, 0));
		
		JPanel playersPanel = new JPanel(new GridBagLayout());
		playersPanel.setBorder(new TitledBorder("Players"));
		
		playersPanel.add(playersTabbedPane, new GridBagConstraints(0, 0, 1, 1, 1.0, 1.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));

		this.add(managerPanel, new GridBagConstraints(0, 0, 1, 1, 0.0, 1.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));
		this.add(playersPanel, new GridBagConstraints(1, 0, 1, 1, 1.0, 1.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));
	}

	private AbstractAction createButtonMethod(final PlayerPanel panel)
	{
		return new AbstractAction("Create")
		{
			public void actionPerformed(ActionEvent evt)
			{
				try
				{
					int port = Integer.valueOf(portTextField.getText());
					String type = (String) typeComboBox.getSelectedItem();

					MatchPanel matchPanel = new MatchPanel();
					NetworkPanel networkPanel = new NetworkPanel();
					DetailPanel detailPanel = null;
					ConfigPanel configPanel = null;
					SingleGameGamer gamer = null;

					Class<?> gamerClass = gamers.get(typeComboBox.getSelectedIndex());
					try {
						gamer = (SingleGameGamer) gamerClass.newInstance();
					} catch(Exception ex) { throw new RuntimeException(ex); }
					detailPanel = gamer.getDetailPanel();
					configPanel = gamer.getConfigPanel();

					gamer.addObserver(matchPanel);
					gamer.addObserver(detailPanel);

					// Registration server stuff
					String addressString = panel.regServerField.getText(); 
					String[] splitAddress = addressString.split(":");
					String regHost = null;
					int regPort = -1;
					if (splitAddress.length > 1) {
			            regHost = splitAddress[0];
			            regPort = Integer.parseInt(splitAddress[1].replace(" ", ""));
					}
					
					String host = panel.ipComboBox.getSelectedItem().toString();
		            
					GamePlayer player = new GamePlayer(host, port, gamer);
					player.addObserver(networkPanel);
					player.setRegistrationServer(regHost, regPort);
					player.start();					

					JTabbedPane tab = new JTabbedPane();
					tab.addTab("Match", matchPanel);
					tab.addTab("Network", networkPanel);
					tab.addTab("Configuration", configPanel);
					tab.addTab("Detail", detailPanel);
					playersTabbedPane.addTab(type + " (" + player.getGamerPort() + ")", tab);
					playersTabbedPane.setSelectedIndex(playersTabbedPane.getTabCount()-1);
				
					panel.setCurrent(tab);
					panel.addPlayer(tab, player);
					
					defaultPort++;
					portTextField.setText(defaultPort.toString());
				}
				catch (Exception e)
				{
					e.printStackTrace();
				}
			}
		};
	}
	
	protected void addPlayer(JTabbedPane tab, GamePlayer player) {
		this.playerMap.put(tab, player);
	}

	protected void setCurrent(JTabbedPane tab) {
		this.currentPane = tab;
	}

	private AbstractAction abortButtonMethod(final PlayerPanel panel) {
		return new AbstractAction("Abort")
		{
			public void actionPerformed(ActionEvent evt)
			{
				panel.abortCurrent();
			}
		};
	}

	protected void abortCurrent() {
		GamePlayer player = playerMap.get(currentPane);
		if (player != null) {
			player.abortAll();
		}
	}
	
	// The following window methods are for the PlayerPanel application as a whole.
	
	@Override
	public void windowActivated(WindowEvent arg0) {	}

	@Override
	public void windowClosed(WindowEvent arg0) { }

	@Override
	public void windowClosing(WindowEvent arg0) {
		for (GamePlayer player : this.playerMap.values()) {
			player.interrupt();
		}
	}

	@Override
	public void windowDeactivated(WindowEvent arg0) {}

	@Override
	public void windowDeiconified(WindowEvent arg0) {}

	@Override
	public void windowIconified(WindowEvent arg0) {}

	@Override
	public void windowOpened(WindowEvent arg0) {}

	@Override
	public void mouseClicked(MouseEvent arg0) {
		this.currentPane = (JTabbedPane) this.playersTabbedPane.getSelectedComponent();
	}

	@Override
	public void mouseEntered(MouseEvent arg0) {	}

	@Override
	public void mouseExited(MouseEvent arg0) {	}

	@Override
	public void mousePressed(MouseEvent arg0) {	}

	@Override
	public void mouseReleased(MouseEvent arg0) { }
}