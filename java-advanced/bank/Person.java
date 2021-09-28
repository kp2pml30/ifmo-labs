
package rmi;

import java.rmi.*;
import java.util.List;

public interface Person extends Remote {
	String getName() throws RemoteException;
	String getSurname() throws RemoteException;
	String getPassport() throws RemoteException;

	List<Account> getAccounts() throws RemoteException;
	Account findAccount(String id) throws RemoteException;

	Account createAccount(String id) throws RemoteException;
}
