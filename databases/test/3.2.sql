delete from Runs
where SessionId in (
	select Sessions.SessionId
	from Sessions natural join Teams
	where TeamName = :TeamName
)