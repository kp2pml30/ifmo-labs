delete from Runs
where SessionId in (
	select Sessions.SessionId
	from Sessions
	where ContestId = :ContestId
)