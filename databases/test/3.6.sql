insert into Runs
select
	(select max(oi.RunId) + Runs.SessionId * 100 + Runs.Letter from Runs oi) RunId,
	SessionId,
	Letter,
	(
		select max(r.SubmitTime) + 1
		from Runs r
		where
			r.SessionId = Runs.SessionId
			and r.Letter = Runs.Letter
	) as SubmitTime,
	1 as Accepted
from Runs
where
	SessionId not in (select SessionId from Runs r where r.Letter = Runs.Letter and r.Accepted = 1)