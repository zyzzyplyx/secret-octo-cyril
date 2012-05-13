package util.networking;

import java.io.IOException;
import java.net.Inet4Address;
import java.net.InetAddress;
import java.net.NetworkInterface;
import java.net.Socket;
import java.net.SocketException;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.List;

public class NetworkUtils {
	
	public static List<InetAddress> getLocalIPList() throws SocketException, UnknownHostException {
		List<InetAddress> result = new ArrayList<InetAddress>();
		
		Enumeration<NetworkInterface> nets = NetworkInterface.getNetworkInterfaces();
	    for (NetworkInterface net : Collections.list(nets)) {
	    	if (!net.isLoopback() && !net.isVirtual() && !net.isPointToPoint() && net.isUp()) {
	    		for (InetAddress curAddress : Collections.list(net.getInetAddresses())) {
	    			
	    			if (curAddress != null && !curAddress.isMulticastAddress()
	    				&& curAddress instanceof Inet4Address) {
	    				result.add(curAddress);
	    			}
	    		}
	    	}
	    }
	    
	    // Add the loopback address at the end
	    result.add(InetAddress.getLocalHost());
	    
	    return result;
	}
	
	public static InetAddress getALocalIPAddress() throws SocketException, UnknownHostException {
		List<InetAddress> addresses = getLocalIPList();
		return addresses.get(0);
	}
	
	public static Socket getSocketFromString(String s) throws UnknownHostException, IOException {
		Socket result = null;
		String[] splitAddress = s.split(":");
		if (splitAddress.length > 1) {
	        String hostname = splitAddress[0];
	        int port = Integer.parseInt(splitAddress[1]);
	        result = new Socket(hostname, port);
		}
		return result;
	}
}
