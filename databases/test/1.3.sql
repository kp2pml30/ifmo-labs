select RunId, SessionId, Letter, SubmitTime
from Sessions natural join Runs
where Accepted = 1 and ContestId = :ContestId