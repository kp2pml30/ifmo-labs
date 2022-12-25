select ContestId, Letter
from Problems
where not exists (
	select * from Sessions, Runs
	where
		Sessions.SessionId = Runs.SessionId
		and Sessions.ContestId = Problems.ContestId
		and Runs.Letter = Problems.Letter
		and Accepted = 1
)