update Runs
set Accepted = 1
where
	Runs.SubmitTime = (select max(SubmitTime) from Runs r where r.SessionId = Runs.SessionId)